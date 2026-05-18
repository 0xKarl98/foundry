use super::MissingEventsAccessControl;
use crate::{
    linter::{LateLintPass, LintContext},
    sol::{Severity, SolLint},
};
use solar::{
    ast,
    interface::{data_structures::Never, sym},
    sema::hir::{
        self, BinOpKind, ElementaryType, ExprKind, ItemId, Res, StmtKind, TypeKind, Visit,
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
        if !is_entry_point(func) || !is_protected(hir, func) {
            return;
        }

        let Some(body) = func.body else { return };
        if contains_event(hir, body) || modifiers_contain_event(hir, func) {
            return;
        }

        let access_control_vars = contract_modifier_state_reads(hir, func);
        if access_control_vars.is_empty() {
            return;
        }

        let mut analyzer = Analyzer::new(hir, &access_control_vars);
        for stmt in body.stmts {
            let _ = analyzer.visit_stmt(stmt);
        }

        for finding in analyzer.findings {
            ctx.emit(&MISSING_EVENTS_ACCESS_CONTROL, finding);
        }
    }
}

fn is_entry_point(func: &hir::Function<'_>) -> bool {
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
    let var = hir.variable(var_id);
    var.kind.is_state() && matches!(var.ty.kind, TypeKind::Elementary(ElementaryType::Address(_)))
}

fn is_address_local(hir: &hir::Hir<'_>, var_id: hir::VariableId) -> bool {
    let var = hir.variable(var_id);
    !var.kind.is_state() && matches!(var.ty.kind, TypeKind::Elementary(ElementaryType::Address(_)))
}

fn is_protected(hir: &hir::Hir<'_>, func: &hir::Function<'_>) -> bool {
    if let Some(body) = func.body
        && body_has_msg_sender_check(hir, body)
    {
        return true;
    }

    func.modifiers.iter().any(|invocation| {
        let Some(modifier_id) = invocation.id.as_function() else { return false };
        let modifier = hir.function(modifier_id);
        modifier.body.is_some_and(|body| body_has_msg_sender_check(hir, body))
    })
}

fn body_has_msg_sender_check(hir: &hir::Hir<'_>, body: hir::Block<'_>) -> bool {
    let mut visitor = MsgSenderCheckVisitor { hir, found: false };
    for stmt in body.stmts {
        let _ = visitor.visit_stmt(stmt);
        if visitor.found {
            return true;
        }
    }
    false
}

struct MsgSenderCheckVisitor<'hir> {
    hir: &'hir hir::Hir<'hir>,
    found: bool,
}

impl<'hir> Visit<'hir> for MsgSenderCheckVisitor<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
        if let StmtKind::If(cond, _, _) = stmt.kind
            && contains_msg_sender(cond)
        {
            self.found = true;
            return ControlFlow::Continue(());
        }
        self.walk_stmt(stmt)
    }

    fn visit_expr(&mut self, expr: &'hir hir::Expr<'hir>) -> ControlFlow<Self::BreakValue> {
        if let ExprKind::Call(callee, args, _) = &expr.kind
            && is_require_or_assert(callee)
            && args.exprs().next().is_some_and(contains_msg_sender)
        {
            self.found = true;
            return ControlFlow::Continue(());
        }
        self.walk_expr(expr)
    }
}

fn is_require_or_assert(callee: &hir::Expr<'_>) -> bool {
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
    func.modifiers.iter().any(|invocation| {
        let Some(modifier_id) = invocation.id.as_function() else { return false };
        let modifier = hir.function(modifier_id);
        modifier.body.is_some_and(|body| contains_event(hir, body))
    })
}

fn contains_event(hir: &hir::Hir<'_>, body: hir::Block<'_>) -> bool {
    let mut visitor = EventVisitor { hir, found: false };
    for stmt in body.stmts {
        let _ = visitor.visit_stmt(stmt);
        if visitor.found {
            return true;
        }
    }
    false
}

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
        if matches!(stmt.kind, StmtKind::Emit(_)) {
            self.found = true;
            return ControlFlow::Continue(());
        }
        self.walk_stmt(stmt)
    }
}

fn contract_modifier_state_reads(
    hir: &hir::Hir<'_>,
    func: &hir::Function<'_>,
) -> HashSet<hir::VariableId> {
    let mut reads = HashSet::new();
    let Some(contract_id) = func.contract else { return reads };

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

    for invocation in func.modifiers {
        collect_invocation_access_control_vars(hir, invocation, &mut reads);
    }

    reads
}

fn is_access_control_modifier(hir: &hir::Hir<'_>, body: hir::Block<'_>) -> bool {
    body_has_msg_sender_check(hir, body)
}

fn collect_invocation_access_control_vars(
    hir: &hir::Hir<'_>,
    invocation: &hir::Modifier<'_>,
    out: &mut HashSet<hir::VariableId>,
) {
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
        let Some(index) = modifier.parameters.iter().position(|&id| id == param) else {
            continue;
        };
        let Some(arg) = invocation.args.exprs().nth(index) else { continue };
        let mut arg_vars = HashSet::new();
        collect_state_vars(arg, &mut arg_vars);
        out.extend(arg_vars.into_iter().filter(|&var_id| is_address_state_var(hir, var_id)));
    }
}

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
                if let ExprKind::Index(base, Some(index)) = &callee.kind {
                    if contains_msg_sender(index) {
                        self.collect_non_sender_vars(base);
                    }
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

impl<'hir> Visit<'hir> for AccessControlReadCollector<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
        if let StmtKind::If(cond, then, else_) = stmt.kind {
            self.collect_access_vars(cond);
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
                if let Some(cond) = args.exprs().next() {
                    self.collect_access_vars(cond);
                }
                return ControlFlow::Continue(());
            }
            ExprKind::Assign(lhs, op, rhs) => {
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

struct Analyzer<'hir> {
    hir: &'hir hir::Hir<'hir>,
    access_control_vars: &'hir HashSet<hir::VariableId>,
    taint: HashMap<hir::VariableId, bool>,
    findings: Vec<solar::interface::Span>,
    emitted_vars: HashSet<hir::VariableId>,
}

impl<'hir> Analyzer<'hir> {
    fn new(hir: &'hir hir::Hir<'hir>, access_control_vars: &'hir HashSet<hir::VariableId>) -> Self {
        Self {
            hir,
            access_control_vars,
            taint: HashMap::new(),
            findings: Vec::new(),
            emitted_vars: HashSet::new(),
        }
    }

    fn is_tainted(&self, expr: &hir::Expr<'_>) -> bool {
        match &expr.kind {
            ExprKind::Ident(reses) => reses.iter().any(|res| match res {
                Res::Item(ItemId::Variable(var_id)) => {
                    let var = self.hir.variable(*var_id);
                    matches!(var.kind, hir::VarKind::FunctionParam | hir::VarKind::TryCatch)
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
}

impl<'hir> Visit<'hir> for Analyzer<'hir> {
    type BreakValue = Never;

    fn hir(&self) -> &'hir hir::Hir<'hir> {
        self.hir
    }

    fn visit_stmt(&mut self, stmt: &'hir hir::Stmt<'hir>) -> ControlFlow<Self::BreakValue> {
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
    let mut vars = Vec::new();
    collect_state_write_lhs_vars(hir, expr, &mut vars);
    vars
}

fn collect_state_write_lhs_vars(
    hir: &hir::Hir<'_>,
    expr: &hir::Expr<'_>,
    vars: &mut Vec<(hir::VariableId, solar::interface::Span)>,
) {
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
