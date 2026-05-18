use super::MissingEventsAccessControl;
use crate::{
    linter::{LateLintPass, LintContext},
    sol::{Severity, SolLint},
};
use solar::{
    ast,
    interface::{data_structures::Never, sym},
    sema::hir::{
        self, BinOpKind, ElementaryType, ExprKind, ItemId, Res, StmtKind, TypeKind, UnOpKind, Visit,
    },
};
use std::{
    collections::{HashMap, HashSet},
    ops::ControlFlow,
};

declare_forge_lint!(
    MISSING_EVENTS_ACCESS_CONTROL,
    Severity::Low,
    "missing-events-access-control",
    "access control state change should emit an event"
);

impl<'hir> LateLintPass<'hir> for MissingEventsAccessControl {
    fn check_function(
        &mut self,
        ctx: &LintContext,
        hir: &'hir hir::Hir<'hir>,
        func: &'hir hir::Function<'hir>,
    ) {
        // This lint only applies to externally reachable, state-changing functions that are
        // actually gated by access-control logic.
        if !is_entry_point(func) || !is_protected(hir, func) {
            return;
        }

        let Some(body) = func.body else { return };
        // Any event emitted by the function body or its invoked modifiers is treated as
        // satisfying the audit trail requirement for the protected state update.
        if contains_event(hir, body) || modifiers_contain_event(hir, func) {
            return;
        }

        // Build the set of address state variables used as access-control authorities, including
        // inline guards and parameterized modifier invocations such as `only(admin)`.
        let access_control_vars = access_control_state_vars(hir, func);
        if access_control_vars.is_empty() {
            return;
        }

        // Analyze both the function body and invoked modifier bodies because either location can
        // write the protected access-control state during this external call.
        let mut analyzer = Analyzer::new(hir, &access_control_vars, func.parameters);
        for stmt in body.stmts {
            let _ = analyzer.visit_stmt(stmt);
        }
        for modifier in func.modifiers {
            analyzer.visit_modifier_invocation(modifier);
        }

        for finding in analyzer.findings {
            ctx.emit(&MISSING_EVENTS_ACCESS_CONTROL, finding);
        }
    }
}

fn is_entry_point(func: &hir::Function<'_>) -> bool {
    // Limit the lint to ordinary external/public functions that can mutate state after deployment.
    if func.is_constructor() {
        return false;
    }
    if matches!(func.state_mutability, ast::StateMutability::Pure | ast::StateMutability::View) {
        return false;
    }
    func.kind.is_function()
        && matches!(func.visibility, ast::Visibility::Public | ast::Visibility::External)
}

fn is_address_state_var(hir: &hir::Hir<'_>, var_id: hir::VariableId) -> bool {
    // Access-control authorities tracked by this lint must be address-typed state variables.
    let var = hir.variable(var_id);
    var.kind.is_state() && matches!(var.ty.kind, TypeKind::Elementary(ElementaryType::Address(_)))
}

fn is_address_local(hir: &hir::Hir<'_>, var_id: hir::VariableId) -> bool {
    // Local address values can carry taint from user input but are not themselves tracked state.
    let var = hir.variable(var_id);
    !var.kind.is_state() && matches!(var.ty.kind, TypeKind::Elementary(ElementaryType::Address(_)))
}

fn is_protected(hir: &hir::Hir<'_>, func: &hir::Function<'_>) -> bool {
    // A function is protected when either its body or an invoked modifier gates execution on
    // msg.sender against an access-control value.
    if let Some(body) = func.body
        && body_has_msg_sender_gate(hir, body, false)
    {
        return true;
    }

    func.modifiers.iter().any(|invocation| {
        let Some(modifier_id) = invocation.id.as_function() else { return false };
        let modifier = hir.function(modifier_id);
        modifier.body.is_some_and(|body| body_has_msg_sender_gate(hir, body, true))
    })
}

fn body_has_msg_sender_gate(hir: &hir::Hir<'_>, body: hir::Block<'_>, allow_params: bool) -> bool {
    // Walk a body looking for a msg.sender check that actually gates continued execution.
    let mut visitor = MsgSenderGateVisitor { hir, allow_params, found: false };
    for stmt in body.stmts {
        let _ = visitor.visit_stmt(stmt);
        if visitor.found {
            return true;
        }
    }
    false
}

fn msg_sender_if_gates_execution(
    hir: &hir::Hir<'_>,
    cond: &hir::Expr<'_>,
    then: &hir::Stmt<'_>,
    else_: Option<&hir::Stmt<'_>>,
    allow_params: bool,
) -> bool {
    // An if-condition is a gate only when it compares msg.sender to an access-control value and
    // the unauthorized branch exits before protected writes can run.
    if !condition_has_access_control_value(hir, cond, allow_params) {
        return false;
    }

    match sender_condition_allows(cond) {
        Some(true) => else_.is_some_and(stmt_exits),
        Some(false) => stmt_exits(then),
        None => false,
    }
}

fn sender_condition_allows(expr: &hir::Expr<'_>) -> Option<bool> {
    // Return whether the condition allows execution for msg.sender; None means the shape is
    // unsupported for access-control gating.
    match &expr.peel_parens().kind {
        ExprKind::Binary(lhs, op, rhs) if contains_msg_sender(lhs) || contains_msg_sender(rhs) => {
            match op.kind {
                BinOpKind::Eq => Some(true),
                BinOpKind::Ne => Some(false),
                _ => None,
            }
        }
        ExprKind::Unary(op, inner) if op.kind == UnOpKind::Not => sender_condition_allows(inner)
            .map(|allows| !allows)
            .or_else(|| contains_msg_sender(inner).then_some(false)),
        ExprKind::Call(_, _, _) | ExprKind::Index(_, _) if contains_msg_sender(expr) => Some(true),
        _ => None,
    }
}

fn stmt_exits(stmt: &hir::Stmt<'_>) -> bool {
    // Conservatively identify statements that stop execution before a protected write can run.
    match stmt.kind {
        StmtKind::Return(_) | StmtKind::Revert(_) => true,
        StmtKind::Block(block) | StmtKind::UncheckedBlock(block) => block_exits(block),
        StmtKind::If(_, then, Some(else_)) => stmt_exits(then) && stmt_exits(else_),
        _ => false,
    }
}

fn block_exits(block: hir::Block<'_>) -> bool {
    // A block exits only if its final statement exits on all reachable paths.
    block.stmts.last().is_some_and(stmt_exits)
}

// Finds require/assert checks and if-guards that constrain execution by msg.sender.
struct MsgSenderGateVisitor<'hir> {
    hir: &'hir hir::Hir<'hir>,
    allow_params: bool,
    found: bool,
}

impl<'hir> Visit<'hir> for MsgSenderGateVisitor<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
        // Treat if-statements as guards only when the unauthorized path exits.
        if let StmtKind::If(cond, then, else_) = stmt.kind
            && msg_sender_if_gates_execution(self.hir, cond, then, else_, self.allow_params)
        {
            self.found = true;
            return ControlFlow::Continue(());
        }
        self.walk_stmt(stmt)
    }

    fn visit_expr(&mut self, expr: &'hir hir::Expr<'hir>) -> ControlFlow<Self::BreakValue> {
        // require/assert calls are guards only when their condition compares msg.sender with an
        // access-control value.
        if let ExprKind::Call(callee, args, _) = &expr.kind
            && is_require_or_assert(callee)
            && args.exprs().next().is_some_and(|cond| {
                condition_has_access_control_value(self.hir, cond, self.allow_params)
            })
        {
            self.found = true;
            return ControlFlow::Continue(());
        }
        self.walk_expr(expr)
    }
}

fn is_require_or_assert(callee: &hir::Expr<'_>) -> bool {
    // Only Solidity builtins are treated as guard calls; user-defined functions are ignored.
    if let ExprKind::Ident(reses) = &callee.kind {
        return reses.iter().any(|res| {
            if let Res::Builtin(builtin) = res {
                let name = builtin.name();
                name == sym::require || name == sym::assert
            } else {
                false
            }
        });
    }
    false
}

fn contains_msg_sender(expr: &hir::Expr<'_>) -> bool {
    // Recursively inspect an expression tree for the concrete msg.sender member access.
    if is_msg_sender(expr) {
        return true;
    }

    match &expr.kind {
        ExprKind::Assign(lhs, _, rhs) | ExprKind::Binary(lhs, _, rhs) => {
            contains_msg_sender(lhs) || contains_msg_sender(rhs)
        }
        ExprKind::Call(callee, args, opts) => {
            contains_msg_sender(callee)
                || args.exprs().any(contains_msg_sender)
                || opts.is_some_and(|opts| opts.iter().any(|arg| contains_msg_sender(&arg.value)))
        }
        ExprKind::Delete(inner)
        | ExprKind::Member(inner, _)
        | ExprKind::Payable(inner)
        | ExprKind::Unary(_, inner) => contains_msg_sender(inner),
        ExprKind::Index(base, index) => {
            contains_msg_sender(base) || index.is_some_and(contains_msg_sender)
        }
        ExprKind::Slice(base, start, end) => {
            contains_msg_sender(base)
                || start.is_some_and(contains_msg_sender)
                || end.is_some_and(contains_msg_sender)
        }
        ExprKind::Ternary(cond, then, else_) => {
            contains_msg_sender(cond) || contains_msg_sender(then) || contains_msg_sender(else_)
        }
        ExprKind::Tuple(exprs) => exprs.iter().copied().flatten().any(contains_msg_sender),
        ExprKind::Array(exprs) => exprs.iter().any(contains_msg_sender),
        _ => false,
    }
}

fn collect_state_vars(expr: &hir::Expr<'_>, out: &mut HashSet<hir::VariableId>) {
    // Collect variable references from an expression so callers can filter state/address
    // candidates.
    match &expr.kind {
        ExprKind::Ident(reses) => {
            for res in *reses {
                if let Res::Item(ItemId::Variable(var_id)) = res {
                    out.insert(*var_id);
                }
            }
        }
        ExprKind::Assign(lhs, _, rhs) | ExprKind::Binary(lhs, _, rhs) => {
            collect_state_vars(lhs, out);
            collect_state_vars(rhs, out);
        }
        ExprKind::Call(callee, args, opts) => {
            collect_state_vars(callee, out);
            for arg in args.exprs() {
                collect_state_vars(arg, out);
            }
            if let Some(opts) = opts {
                for opt in *opts {
                    collect_state_vars(&opt.value, out);
                }
            }
        }
        ExprKind::Delete(inner)
        | ExprKind::Member(inner, _)
        | ExprKind::Payable(inner)
        | ExprKind::Unary(_, inner) => collect_state_vars(inner, out),
        ExprKind::Index(base, index) => {
            collect_state_vars(base, out);
            if let Some(index) = index {
                collect_state_vars(index, out);
            }
        }
        ExprKind::Slice(base, start, end) => {
            collect_state_vars(base, out);
            if let Some(start) = start {
                collect_state_vars(start, out);
            }
            if let Some(end) = end {
                collect_state_vars(end, out);
            }
        }
        ExprKind::Ternary(cond, then, else_) => {
            collect_state_vars(cond, out);
            collect_state_vars(then, out);
            collect_state_vars(else_, out);
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs.iter().copied().flatten() {
                collect_state_vars(expr, out);
            }
        }
        ExprKind::Array(exprs) => {
            for expr in *exprs {
                collect_state_vars(expr, out);
            }
        }
        _ => {}
    }
}

fn is_msg_sender(expr: &hir::Expr<'_>) -> bool {
    // Match the builtin msg.sender access exactly, not user-defined lookalikes.
    matches!(
        &expr.kind,
        ExprKind::Member(base, member)
            if member.name == sym::sender
            && matches!(
                &base.kind,
                ExprKind::Ident(reses)
                    if reses.iter().any(|res| {
                        matches!(res, Res::Builtin(builtin) if builtin.name() == sym::msg)
                    })
            )
    )
}

fn modifiers_contain_event(hir: &hir::Hir<'_>, func: &hir::Function<'_>) -> bool {
    // Events emitted from invoked modifiers also satisfy the lint's event requirement.
    func.modifiers.iter().any(|invocation| {
        let Some(modifier_id) = invocation.id.as_function() else { return false };
        let modifier = hir.function(modifier_id);
        modifier.body.is_some_and(|body| contains_event(hir, body))
    })
}

fn contains_event(hir: &hir::Hir<'_>, body: hir::Block<'_>) -> bool {
    // Scan a body for any emit statement, including nested statements reached by the visitor.
    let mut visitor = EventVisitor { hir, found: false };
    for stmt in body.stmts {
        let _ = visitor.visit_stmt(stmt);
        if visitor.found {
            return true;
        }
    }
    false
}

// Finds whether a body emits an event.
struct EventVisitor<'hir> {
    hir: &'hir hir::Hir<'hir>,
    found: bool,
}

impl<'hir> Visit<'hir> for EventVisitor<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
        // Any emit statement is enough; this lint does not validate event names or arguments.
        if matches!(stmt.kind, StmtKind::Emit(_)) {
            self.found = true;
            return ControlFlow::Continue(());
        }
        self.walk_stmt(stmt)
    }
}

fn access_control_state_vars(
    hir: &hir::Hir<'_>,
    func: &hir::Function<'_>,
) -> HashSet<hir::VariableId> {
    // Collect address state variables that act as authorities for access control in this contract.
    let mut reads = HashSet::new();

    if let Some(body) = func.body {
        // Include inline guards such as `require(msg.sender == owner)` in the current function.
        collect_body_access_control_state_vars(hir, body, &mut reads);
    }

    let Some(contract_id) = func.contract else { return reads };

    // Include state variables read directly by access-control modifier definitions.
    for item in hir.contract_items(contract_id) {
        let hir::Item::Function(modifier) = item else { continue };
        if !matches!(modifier.kind, hir::FunctionKind::Modifier) {
            continue;
        }
        let Some(body) = modifier.body else { continue };
        if !is_access_control_modifier(hir, body) {
            continue;
        }

        let mut collector = AccessControlReadCollector::new(hir);
        for stmt in body.stmts {
            let _ = collector.visit_stmt(stmt);
        }
        reads.extend(
            collector.state_vars.into_iter().filter(|&var_id| is_address_state_var(hir, var_id)),
        );
    }

    // Include state variables passed into parameterized access-control modifiers like
    // `only(admin)`.
    for item in hir.contract_items(contract_id) {
        let hir::Item::Function(func) = item else { continue };
        for invocation in func.modifiers {
            collect_invocation_access_control_vars(hir, invocation, &mut reads);
        }
    }

    reads
}

fn is_access_control_modifier(hir: &hir::Hir<'_>, body: hir::Block<'_>) -> bool {
    // Modifier parameters may stand for access-control authorities at each invocation site.
    body_has_msg_sender_gate(hir, body, true)
}

fn collect_invocation_access_control_vars(
    hir: &hir::Hir<'_>,
    invocation: &hir::Modifier<'_>,
    out: &mut HashSet<hir::VariableId>,
) {
    // Map authority reads inside a parameterized modifier back to the state variables passed by
    // this invocation.
    let Some(modifier_id) = invocation.id.as_function() else { return };
    let modifier = hir.function(modifier_id);
    let Some(body) = modifier.body else { return };
    if !is_access_control_modifier(hir, body) {
        return;
    }

    let mut collector = AccessControlReadCollector::new(hir);
    for stmt in body.stmts {
        let _ = collector.visit_stmt(stmt);
    }

    for var_id in collector.state_vars {
        if is_address_state_var(hir, var_id) {
            out.insert(var_id);
        }
    }

    for param in collector.params {
        // For `modifier only(address who)`, an invocation `only(admin)` makes `admin` the
        // authority.
        let Some(arg) = invocation_arg_for_param(hir, modifier, invocation, param) else {
            continue;
        };
        let mut arg_vars = HashSet::new();
        collect_state_vars(arg, &mut arg_vars);
        out.extend(arg_vars.into_iter().filter(|&var_id| is_address_state_var(hir, var_id)));
    }
}

// Collects state variables and modifier parameters that are read in msg.sender guard conditions.
struct AccessControlReadCollector<'hir> {
    hir: &'hir hir::Hir<'hir>,
    state_vars: HashSet<hir::VariableId>,
    params: HashSet<hir::VariableId>,
}

impl<'hir> AccessControlReadCollector<'hir> {
    fn new(hir: &'hir hir::Hir<'hir>) -> Self {
        Self { hir, state_vars: HashSet::new(), params: HashSet::new() }
    }

    fn collect_access_vars(&mut self, expr: &'hir hir::Expr<'hir>) {
        // In a sender guard, only the side opposite msg.sender can name the access authority.
        match &expr.kind {
            ExprKind::Binary(lhs, op, rhs) if matches!(op.kind, BinOpKind::Eq | BinOpKind::Ne) => {
                if contains_msg_sender(lhs) {
                    self.collect_non_sender_vars(rhs);
                } else if contains_msg_sender(rhs) {
                    self.collect_non_sender_vars(lhs);
                } else {
                    self.collect_access_vars(lhs);
                    self.collect_access_vars(rhs);
                }
            }
            ExprKind::Binary(lhs, op, rhs) if matches!(op.kind, BinOpKind::And | BinOpKind::Or) => {
                self.collect_access_vars(lhs);
                self.collect_access_vars(rhs);
            }
            ExprKind::Call(callee, args, _) => {
                if let ExprKind::Index(base, Some(index)) = &callee.kind
                    && contains_msg_sender(index)
                {
                    self.collect_non_sender_vars(base);
                }
                for arg in args.exprs() {
                    self.collect_access_vars(arg);
                }
            }
            ExprKind::Unary(_, inner) | ExprKind::Payable(inner) | ExprKind::Member(inner, _) => {
                self.collect_access_vars(inner)
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs.iter().copied().flatten() {
                    self.collect_access_vars(expr);
                }
            }
            _ => {}
        }
    }

    fn collect_non_sender_vars(&mut self, expr: &'hir hir::Expr<'hir>) {
        // Record authority candidates from the non-sender side: state vars directly, params for
        // later invocation-site mapping.
        match &expr.kind {
            ExprKind::Ident(reses) => {
                for res in *reses {
                    if let Res::Item(ItemId::Variable(var_id)) = res {
                        let var = self.hir.variable(*var_id);
                        if var.kind.is_state() {
                            self.state_vars.insert(*var_id);
                        } else if matches!(var.kind, hir::VarKind::FunctionParam) {
                            self.params.insert(*var_id);
                        }
                    }
                }
            }
            ExprKind::Assign(lhs, _, rhs) | ExprKind::Binary(lhs, _, rhs) => {
                self.collect_non_sender_vars(lhs);
                self.collect_non_sender_vars(rhs);
            }
            ExprKind::Call(callee, args, opts) => {
                self.collect_non_sender_vars(callee);
                for arg in args.exprs() {
                    self.collect_non_sender_vars(arg);
                }
                if let Some(opts) = opts {
                    for opt in *opts {
                        self.collect_non_sender_vars(&opt.value);
                    }
                }
            }
            ExprKind::Delete(inner)
            | ExprKind::Member(inner, _)
            | ExprKind::Payable(inner)
            | ExprKind::Unary(_, inner) => self.collect_non_sender_vars(inner),
            ExprKind::Index(base, index) => {
                self.collect_non_sender_vars(base);
                if let Some(index) = index {
                    self.collect_non_sender_vars(index);
                }
            }
            ExprKind::Slice(base, start, end) => {
                self.collect_non_sender_vars(base);
                if let Some(start) = start {
                    self.collect_non_sender_vars(start);
                }
                if let Some(end) = end {
                    self.collect_non_sender_vars(end);
                }
            }
            ExprKind::Ternary(cond, then, else_) => {
                self.collect_non_sender_vars(cond);
                self.collect_non_sender_vars(then);
                self.collect_non_sender_vars(else_);
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs.iter().copied().flatten() {
                    self.collect_non_sender_vars(expr);
                }
            }
            ExprKind::Array(exprs) => {
                for expr in *exprs {
                    self.collect_non_sender_vars(expr);
                }
            }
            _ => {}
        }
    }
}

fn condition_has_access_control_value(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
    allow_params: bool,
) -> bool {
    // A sender condition is access control only if it references an address state authority, or an
    // allowed modifier parameter that can map to one.
    let mut collector = AccessControlReadCollector::new(hir);
    collector.collect_access_vars(expr);
    (allow_params && collector.params.iter().any(|&var_id| is_address_local(hir, var_id)))
        || collector.state_vars.iter().any(|&var_id| is_address_state_var(hir, var_id))
}

fn collect_body_access_control_state_vars(
    hir: &hir::Hir<'_>,
    body: hir::Block<'_>,
    out: &mut HashSet<hir::VariableId>,
) {
    // Collect access-control authorities from inline guards in a function body.
    let mut collector = AccessControlReadCollector::new(hir);
    for stmt in body.stmts {
        let _ = collector.visit_stmt(stmt);
    }
    out.extend(
        collector.state_vars.into_iter().filter(|&var_id| is_address_state_var(hir, var_id)),
    );
}

// Visits guard-shaped code to collect the authority variables referenced by msg.sender checks.
impl<'hir> Visit<'hir> for AccessControlReadCollector<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
        // Only if-statements that truly gate execution contribute access-control reads.
        if let StmtKind::If(cond, then, else_) = stmt.kind {
            if msg_sender_if_gates_execution(self.hir, cond, then, else_, true) {
                self.collect_access_vars(cond);
            }
            let _ = self.visit_stmt(then);
            if let Some(else_) = else_ {
                let _ = self.visit_stmt(else_);
            }
            return ControlFlow::Continue(());
        }
        self.walk_stmt(stmt)
    }

    fn visit_expr(&mut self, expr: &'hir hir::Expr<'hir>) -> ControlFlow<Self::BreakValue> {
        match &expr.kind {
            ExprKind::Call(callee, args, _) if is_require_or_assert(callee) => {
                // require/assert conditions contribute reads only when they compare against an
                // access-control value.
                if let Some(cond) = args.exprs().next()
                    && condition_has_access_control_value(self.hir, cond, true)
                {
                    self.collect_access_vars(cond);
                }
                return ControlFlow::Continue(());
            }
            ExprKind::Assign(lhs, op, rhs) => {
                // Assignments are not guards; visit only value-producing sides to avoid counting a
                // plain lhs write as an access-control read.
                if op.is_some() {
                    let _ = self.visit_expr(lhs);
                }
                let _ = self.visit_expr(rhs);
                return ControlFlow::Continue(());
            }
            ExprKind::Delete(_) => return ControlFlow::Continue(()),
            _ => {}
        }
        self.walk_expr(expr)
    }
}

// Tracks tainted address values and reports tainted writes into access-control state variables.
struct Analyzer<'hir> {
    hir: &'hir hir::Hir<'hir>,
    access_control_vars: &'hir HashSet<hir::VariableId>,
    entry_params: &'hir [hir::VariableId],
    taint: HashMap<hir::VariableId, bool>,
    modifier_param_taint: HashMap<hir::VariableId, bool>,
    findings: Vec<solar::interface::Span>,
    emitted_vars: HashSet<hir::VariableId>,
}

impl<'hir> Analyzer<'hir> {
    fn new(
        hir: &'hir hir::Hir<'hir>,
        access_control_vars: &'hir HashSet<hir::VariableId>,
        entry_params: &'hir [hir::VariableId],
    ) -> Self {
        Self {
            hir,
            access_control_vars,
            entry_params,
            taint: HashMap::new(),
            modifier_param_taint: HashMap::new(),
            findings: Vec::new(),
            emitted_vars: HashSet::new(),
        }
    }

    fn visit_modifier_invocation(&mut self, invocation: &'hir hir::Modifier<'hir>) {
        // Analyze modifier bodies in call context so writes inside modifiers are checked too.
        let Some(modifier_id) = invocation.id.as_function() else { return };
        let modifier = self.hir.function(modifier_id);
        let Some(body) = modifier.body else { return };

        let restore = self.bind_modifier_params(modifier, invocation);
        for stmt in body.stmts {
            let _ = self.visit_stmt(stmt);
        }
        self.restore_modifier_params(restore);
    }

    fn bind_modifier_params(
        &mut self,
        modifier: &'hir hir::Function<'hir>,
        invocation: &'hir hir::Modifier<'hir>,
    ) -> Vec<(hir::VariableId, Option<bool>)> {
        // Temporarily bind modifier parameters to the taint of this invocation's arguments.
        let mut restore = Vec::new();
        for &param in modifier.parameters {
            let tainted = invocation_arg_for_param(self.hir, modifier, invocation, param)
                .is_some_and(|arg| self.is_tainted(arg));
            restore.push((param, self.modifier_param_taint.insert(param, tainted)));
        }
        restore
    }

    fn restore_modifier_params(&mut self, restore: Vec<(hir::VariableId, Option<bool>)>) {
        // Restore previous modifier parameter bindings after leaving the modifier body.
        for (param, previous) in restore {
            if let Some(previous) = previous {
                self.modifier_param_taint.insert(param, previous);
            } else {
                self.modifier_param_taint.remove(&param);
            }
        }
    }

    fn is_tainted(&self, expr: &hir::Expr<'_>) -> bool {
        // Taint means the value can originate from an entry parameter, modifier argument, builtin,
        // try/catch binding, allocation, or another tainted expression.
        match &expr.kind {
            ExprKind::Ident(reses) => reses.iter().any(|res| match res {
                Res::Item(ItemId::Variable(var_id)) => {
                    let var = self.hir.variable(*var_id);
                    matches!(var.kind, hir::VarKind::TryCatch)
                        || (matches!(var.kind, hir::VarKind::FunctionParam)
                            && self.param_taint(*var_id))
                        || self.taint.get(var_id).copied().unwrap_or(false)
                }
                Res::Builtin(_) => true,
                _ => false,
            }),
            ExprKind::Assign(_, _, rhs)
            | ExprKind::Delete(rhs)
            | ExprKind::Member(rhs, _)
            | ExprKind::Payable(rhs)
            | ExprKind::Unary(_, rhs) => self.is_tainted(rhs),
            ExprKind::Binary(lhs, _, rhs) | ExprKind::Index(lhs, Some(rhs)) => {
                self.is_tainted(lhs) || self.is_tainted(rhs)
            }
            ExprKind::Index(base, None) => self.is_tainted(base),
            ExprKind::Slice(base, start, end) => {
                self.is_tainted(base)
                    || start.is_some_and(|expr| self.is_tainted(expr))
                    || end.is_some_and(|expr| self.is_tainted(expr))
            }
            ExprKind::Ternary(cond, then, else_) => {
                self.is_tainted(cond) || self.is_tainted(then) || self.is_tainted(else_)
            }
            ExprKind::Tuple(exprs) => {
                exprs.iter().copied().flatten().any(|expr| self.is_tainted(expr))
            }
            ExprKind::Array(exprs) => exprs.iter().any(|expr| self.is_tainted(expr)),
            ExprKind::Call(callee, args, opts) => {
                self.is_tainted(callee)
                    || args.exprs().any(|expr| self.is_tainted(expr))
                    || opts.is_some_and(|opts| opts.iter().any(|arg| self.is_tainted(&arg.value)))
            }
            ExprKind::New(_) => true,
            _ => false,
        }
    }

    fn record_write(&mut self, lhs: &hir::Expr<'hir>, rhs: Option<&hir::Expr<'hir>>) {
        // Warn only for tainted writes to known access-control state variables, once per variable.
        let tainted = rhs.is_none_or(|expr| self.is_tainted(expr));
        if !tainted {
            return;
        }

        for (var_id, span) in state_write_lhs_vars(self.hir, lhs) {
            if self.access_control_vars.contains(&var_id) && self.emitted_vars.insert(var_id) {
                self.findings.push(span);
            }
        }
    }

    fn param_taint(&self, var_id: hir::VariableId) -> bool {
        // Explicit local taint assignments override the default entry/modifier parameter taint.
        self.taint.get(&var_id).copied().unwrap_or_else(|| {
            self.entry_params.contains(&var_id)
                || self.modifier_param_taint.get(&var_id).copied().unwrap_or(false)
        })
    }
}

fn invocation_arg_for_param<'hir>(
    hir: &'hir hir::Hir<'hir>,
    modifier: &'hir hir::Function<'hir>,
    invocation: &'hir hir::Modifier<'hir>,
    param: hir::VariableId,
) -> Option<&'hir hir::Expr<'hir>> {
    // Resolve both positional and named modifier arguments to the requested modifier parameter.
    let param_index = modifier.parameters.iter().position(|&id| id == param)?;

    match invocation.args.kind {
        hir::CallArgsKind::Unnamed(args) => args.get(param_index),
        hir::CallArgsKind::Named(args) => {
            let param_name = hir.variable(param).name?.name;
            args.iter().find(|arg| arg.name.name == param_name).map(|arg| &arg.value)
        }
    }
}

// Walks executable code to detect tainted writes to protected access-control state.
impl<'hir> Visit<'hir> for Analyzer<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
        // Initialize local address taint from declaration initializers.
        if let StmtKind::DeclSingle(var_id) = stmt.kind {
            let var = self.hir.variable(var_id);
            if let Some(init) = var.initializer
                && is_address_local(self.hir, var_id)
            {
                self.taint.insert(var_id, self.is_tainted(init));
            }
        }
        self.walk_stmt(stmt)
    }

    fn visit_expr(&mut self, expr: &'hir hir::Expr<'hir>) -> ControlFlow<Self::BreakValue> {
        match &expr.kind {
            ExprKind::Assign(lhs, _, rhs) => {
                // First check state writes, then update local alias taint for subsequent writes.
                self.record_write(lhs, Some(rhs));

                if let Some(local) = lhs_local_var(self.hir, lhs) {
                    self.taint.insert(local, self.is_tainted(rhs));
                }
            }
            ExprKind::Delete(inner) => {
                self.record_write(inner, None);
            }
            _ => {}
        }
        self.walk_expr(expr)
    }
}

fn lhs_local_var(hir: &hir::Hir<'_>, lhs: &hir::Expr<'_>) -> Option<hir::VariableId> {
    // Local address assignments update taint aliases; state writes are handled separately.
    if let ExprKind::Ident(reses) = &lhs.kind {
        for res in *reses {
            if let Res::Item(ItemId::Variable(var_id)) = res
                && is_address_local(hir, *var_id)
            {
                return Some(*var_id);
            }
        }
    }
    None
}

fn state_write_lhs_vars(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
) -> Vec<(hir::VariableId, solar::interface::Span)> {
    // Return every distinct state variable written by this left-hand side expression.
    let mut vars = Vec::new();
    collect_state_write_lhs_vars(hir, expr, &mut vars);
    vars
}

fn collect_state_write_lhs_vars(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
    vars: &mut Vec<(hir::VariableId, solar::interface::Span)>,
) {
    // Peel writable lhs shapes so tuple/member/index assignments report the underlying state var.
    match &expr.kind {
        ExprKind::Ident(reses) => {
            for res in *reses {
                if let Res::Item(ItemId::Variable(var_id)) = res
                    && hir.variable(*var_id).kind.is_state()
                    && !vars.iter().any(|(existing, _)| existing == var_id)
                {
                    vars.push((*var_id, expr.span));
                }
            }
        }
        ExprKind::Index(base, _) | ExprKind::Slice(base, ..) => {
            collect_state_write_lhs_vars(hir, base, vars);
        }
        ExprKind::Member(base, _)
        | ExprKind::Payable(base)
        | ExprKind::Unary(_, base)
        | ExprKind::Delete(base) => collect_state_write_lhs_vars(hir, base, vars),
        ExprKind::Tuple(exprs) => {
            for expr in exprs.iter().copied().flatten() {
                collect_state_write_lhs_vars(hir, expr, vars);
            }
        }
        _ => {}
    }
}
