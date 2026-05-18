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
use std::{collections::HashSet, ops::ControlFlow};

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
        let mut analyzer = Analyzer::new(hir, &access_control_vars);
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
    // Modifier parameters can stand in for address authorities without being tracked state.
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

    func.modifiers.iter().any(|invocation| modifier_invocation_has_msg_sender_gate(hir, invocation))
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

fn modifier_invocation_has_msg_sender_gate(
    hir: &hir::Hir<'_>,
    invocation: &hir::Modifier<'_>,
) -> bool {
    let Some(modifier_id) = invocation.id.as_function() else { return false };
    let modifier = hir.function(modifier_id);
    let Some(body) = modifier.body else { return false };

    let mut collector = AccessControlReadCollector::new(hir);
    for stmt in body.stmts {
        let _ = collector.visit_stmt(stmt);
    }

    if collector.state_vars.into_iter().any(|var_id| is_address_state_var(hir, var_id)) {
        return true;
    }

    collector.params.into_iter().any(|param| {
        invocation_arg_for_param(hir, modifier, invocation, param)
            .is_some_and(|arg| expr_has_address_state_var(hir, arg))
    })
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
    if !condition_has_positive_access_control_value(hir, cond, allow_params) {
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
        // require/assert calls are guards only when the condition positively allows an
        // access-control sender.
        if let ExprKind::Call(callee, args, _) = &expr.kind
            && is_require_or_assert(callee)
            && args.exprs().next().is_some_and(|cond| {
                condition_has_positive_access_control_value(self.hir, cond, self.allow_params)
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

fn collect_address_state_vars(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
    out: &mut HashSet<hir::VariableId>,
) {
    // Stream address state variables from an expression directly into the caller's set.
    match &expr.kind {
        ExprKind::Ident(reses) => {
            for res in *reses {
                if let Res::Item(ItemId::Variable(var_id)) = res
                    && is_address_state_var(hir, *var_id)
                {
                    out.insert(*var_id);
                }
            }
        }
        ExprKind::Assign(lhs, _, rhs) | ExprKind::Binary(lhs, _, rhs) => {
            collect_address_state_vars(hir, lhs, out);
            collect_address_state_vars(hir, rhs, out);
        }
        ExprKind::Call(callee, args, opts) => {
            collect_address_state_vars(hir, callee, out);
            for arg in args.exprs() {
                collect_address_state_vars(hir, arg, out);
            }
            if let Some(opts) = opts {
                for opt in *opts {
                    collect_address_state_vars(hir, &opt.value, out);
                }
            }
        }
        ExprKind::Delete(inner)
        | ExprKind::Member(inner, _)
        | ExprKind::Payable(inner)
        | ExprKind::Unary(_, inner) => collect_address_state_vars(hir, inner, out),
        ExprKind::Index(base, index) => {
            collect_address_state_vars(hir, base, out);
            if let Some(index) = index {
                collect_address_state_vars(hir, index, out);
            }
        }
        ExprKind::Slice(base, start, end) => {
            collect_address_state_vars(hir, base, out);
            if let Some(start) = start {
                collect_address_state_vars(hir, start, out);
            }
            if let Some(end) = end {
                collect_address_state_vars(hir, end, out);
            }
        }
        ExprKind::Ternary(cond, then, else_) => {
            collect_address_state_vars(hir, cond, out);
            collect_address_state_vars(hir, then, out);
            collect_address_state_vars(hir, else_, out);
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs.iter().copied().flatten() {
                collect_address_state_vars(hir, expr, out);
            }
        }
        ExprKind::Array(exprs) => {
            for expr in *exprs {
                collect_address_state_vars(hir, expr, out);
            }
        }
        _ => {}
    }
}

fn expr_has_address_state_var(hir: &hir::Hir<'_>, expr: &hir::Expr<'_>) -> bool {
    let mut vars = HashSet::new();
    collect_address_state_vars(hir, expr, &mut vars);
    !vars.is_empty()
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
        collect_address_state_vars(hir, arg, out);
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

fn condition_has_positive_access_control_value(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
    allow_params: bool,
) -> bool {
    // A sender condition is access control only if it positively allows an address state authority,
    // or an allowed modifier parameter that can map to one.
    if sender_condition_allows(expr) != Some(true) {
        return false;
    }

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
                    && condition_has_positive_access_control_value(self.hir, cond, true)
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

// Reports writes into access-control state variables.
struct Analyzer<'hir> {
    hir: &'hir hir::Hir<'hir>,
    access_control_vars: &'hir HashSet<hir::VariableId>,
    findings: Vec<solar::interface::Span>,
    emitted_vars: HashSet<hir::VariableId>,
}

impl<'hir> Analyzer<'hir> {
    fn new(hir: &'hir hir::Hir<'hir>, access_control_vars: &'hir HashSet<hir::VariableId>) -> Self {
        Self { hir, access_control_vars, findings: Vec::new(), emitted_vars: HashSet::new() }
    }

    fn visit_modifier_invocation(&mut self, invocation: &'hir hir::Modifier<'hir>) {
        // Analyze modifier bodies in call context so writes inside modifiers are checked too.
        let Some(modifier_id) = invocation.id.as_function() else { return };
        let modifier = self.hir.function(modifier_id);
        let Some(body) = modifier.body else { return };

        for stmt in body.stmts {
            let _ = self.visit_stmt(stmt);
        }
    }

    fn record_write(&mut self, lhs: &hir::Expr<'hir>) {
        // Warn for any write to known access-control state variables, once per variable.
        visit_state_write_lhs_vars(self.hir, lhs, &mut |var_id, span| {
            if self.access_control_vars.contains(&var_id) && self.emitted_vars.insert(var_id) {
                self.findings.push(span);
            }
        });
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

// Walks executable code to detect writes to protected access-control state.
impl<'hir> Visit<'hir> for Analyzer<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_expr(&mut self, expr: &'hir hir::Expr<'hir>) -> ControlFlow<Self::BreakValue> {
        match &expr.kind {
            ExprKind::Assign(lhs, _, _) => {
                // Any protected access-control state write needs an event, regardless of rhs
                // origin.
                self.record_write(lhs);
            }
            ExprKind::Delete(inner) => {
                self.record_write(inner);
            }
            _ => {}
        }
        self.walk_expr(expr)
    }
}

fn visit_state_write_lhs_vars(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
    visit: &mut impl FnMut(hir::VariableId, solar::interface::Span),
) {
    // Peel writable lhs shapes and stream each underlying state var directly to the caller.
    match &expr.kind {
        ExprKind::Ident(reses) => {
            for res in *reses {
                if let Res::Item(ItemId::Variable(var_id)) = res
                    && hir.variable(*var_id).kind.is_state()
                {
                    visit(*var_id, expr.span);
                }
            }
        }
        ExprKind::Index(base, _) | ExprKind::Slice(base, ..) => {
            visit_state_write_lhs_vars(hir, base, visit);
        }
        ExprKind::Member(base, _)
        | ExprKind::Payable(base)
        | ExprKind::Unary(_, base)
        | ExprKind::Delete(base) => visit_state_write_lhs_vars(hir, base, visit),
        ExprKind::Tuple(exprs) => {
            for expr in exprs.iter().copied().flatten() {
                visit_state_write_lhs_vars(hir, expr, visit);
            }
        }
        _ => {}
    }
}
