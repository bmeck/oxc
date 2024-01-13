#![allow(clippy::unused_self)]

mod ast_util;
mod fold;
mod options;
mod prepass;
mod util;

use oxc_allocator::{Allocator, Vec};
#[allow(clippy::wildcard_imports)]
use oxc_ast::{ast::*, AstBuilder, VisitMut};
use oxc_span::Span;
use oxc_syntax::{
    operator::{BinaryOperator, UnaryOperator},
    precedence::GetPrecedence,
    NumberBase,
};

pub use self::options::CompressOptions;
use self::{ast_util::MayHaveSideEffects, prepass::Prepass};

pub struct Compressor<'a> {
    ast: AstBuilder<'a>,
    options: CompressOptions,

    prepass: Prepass<'a>,
}

const SPAN: Span = Span::new(0, 0);

impl<'a> Compressor<'a> {
    pub fn new(allocator: &'a Allocator, options: CompressOptions) -> Self {
        Self { ast: AstBuilder::new(allocator), options, prepass: Prepass::new(allocator) }
    }

    pub fn build(mut self, program: &mut Program<'a>) {
        self.prepass.build(program);
        self.visit_program(program);
        println!("{:?}", program);
    }

    /* Utilities */

    /**
     * Represents Infinity reliably
     */
    #[allow(unused)]
    fn create_one_div_zero(&mut self) -> Expression<'a> {
        let left = self.ast.number_literal(SPAN, 1.0, "1", NumberBase::Decimal);
        let left = self.ast.literal_number_expression(left);
        let right = self.ast.number_literal(SPAN, 0.0, "0", NumberBase::Decimal);
        let right = self.ast.literal_number_expression(right);
        self.ast.binary_expression(SPAN, left, BinaryOperator::Division, right)
    }

    /**
     * Represents NegativeInfinity reliably
     */
    #[allow(unused)]
    fn create_one_div_negative_zero(&mut self) -> Expression<'a> {
        let left = self.ast.number_literal(SPAN, 1.0, "1", NumberBase::Decimal);
        let left = self.ast.literal_number_expression(left);
        let right = self.ast.number_literal(SPAN, 0.0, "0", NumberBase::Decimal);
        let right = self.ast.literal_number_expression(right);
        let right = self.ast.unary_expression(SPAN, UnaryOperator::UnaryNegation, right);
        self.ast.binary_expression(SPAN, left, BinaryOperator::Division, right)
    }

    /**
     * Represents NaN reliably
     */
    #[allow(unused)]
    fn create_zero_div_zero(&mut self) -> Expression<'a> {
        let left = self.ast.number_literal(SPAN, 0.0, "0", NumberBase::Decimal);
        let left = self.ast.literal_number_expression(left);
        let right = self.ast.number_literal(SPAN, 0.0, "0", NumberBase::Decimal);
        let right = self.ast.literal_number_expression(right);
        self.ast.binary_expression(SPAN, left, BinaryOperator::Division, right)
    }

    /* Statements */

    /// Remove block from single line blocks
    /// `{ block } -> block`
    #[allow(clippy::only_used_in_recursion)] // `&self` is only used in recursion
    fn compress_block(&self, stmt: &mut Statement<'a>) {
        if let Statement::BlockStatement(block) = stmt {
            // Avoid compressing `if (x) { var x = 1 }` to `if (x) var x = 1` due to different
            // semantics according to AnnexB, which lead to different semantics.
            if block.body.len() == 1 && !matches!(&block.body[0], Statement::Declaration(_)) {
                *stmt = block.body.remove(0);
                self.compress_block(stmt);
            }
        }
    }

    /// Transforms `undefined` => `void 0`
    fn compress_undefined(&self, expr: &mut Expression<'a>) -> bool {
        let Expression::Identifier(ident) = expr else { return false };
        if ident.name == "undefined" {
            // if let Some(reference_id) = ident.reference_id.get() {
            // && self.semantic.symbols().is_global_reference(reference_id)
            *expr = self.ast.void_0();
            return true;
            // }
        }
        false
    }

    /// Transforms `Infinity` => `1/0`
    #[allow(unused)]
    fn compress_infinity(&mut self, expr: &mut Expression<'a>) -> bool {
        let Expression::Identifier(ident) = expr else { return false };
        if ident.name == "Infinity" {
            // if let Some(reference_id) = ident.reference_id.get() {
            //&& self.semantic.symbols().is_global_reference(reference_id)
            *expr = self.create_one_div_zero();
            return true;
            // }
        }
        false
    }

    /// Transforms boolean expression `true` => `!0` `false` => `!1`
    /// Enabled by `compress.booleans`
    fn compress_boolean(&mut self, expr: &mut Expression<'a>) -> bool {
        let Expression::BooleanLiteral(lit) = expr else { return false };
        if self.options.booleans {
            let num = self.ast.number_literal(
                SPAN,
                if lit.value { 0.0 } else { 1.0 },
                if lit.value { "0" } else { "1" },
                NumberBase::Decimal,
            );
            let num = self.ast.literal_number_expression(num);
            *expr = self.ast.unary_expression(SPAN, UnaryOperator::LogicalNot, num);
            return true;
        }
        false
    }

    /// Transforms `typeof foo == "undefined"` into `foo === void 0`
    /// Enabled by `compress.typeofs`
    fn compress_typeof_undefined(&self, expr: &mut BinaryExpression<'a>) {
        if expr.operator.is_equality() && self.options.typeofs {
            if let Expression::UnaryExpression(unary_expr) = &expr.left {
                if unary_expr.operator == UnaryOperator::Typeof {
                    if let Expression::Identifier(ident) = &unary_expr.argument {
                        if expr.right.is_specific_string_literal("undefined") {
                            let left = self.ast.identifier_reference_expression((*ident).clone());
                            let right = self.ast.void_0();
                            let operator = BinaryOperator::StrictEquality;
                            *expr = BinaryExpression { span: SPAN, left, operator, right };
                        }
                    }
                }
            }
        };
    }

    /// Removes extra = from already coerced comparisons
    /// Transforms `typeof foo === "undefined"` into `typeof foo == "undefined`
    /// Enabled by `compress.typeofs`
    fn compress_overly_strict(&self, expr: &mut Expression<'a>) {
        if let Expression::BinaryExpression(bi) = expr {
            match bi.operator {
                BinaryOperator::StrictEquality => {
                    let maybe_left_type = bi.left.evaluate_to_specific_primitive_type();
                    let maybe_right_type = bi.right.evaluate_to_specific_primitive_type();
                    // no side effects, can replace potentially with a literal
                    match (maybe_left_type, maybe_right_type) {
                        (Some(left_type), Some(right_type)) => {
                            let comp = left_type.compare(&right_type);
                            println!("{:?} {:?} {:?}", left_type, right_type, comp);
                            match comp {
                                PrimitiveTypeComparison::Unknown => (),
                                PrimitiveTypeComparison::AlwaysSameType => {
                                    bi.operator = BinaryOperator::Equality;
                                }
                                PrimitiveTypeComparison::AlwaysSameTypeAndValue => {
                                    if !bi.left.may_have_side_effects()
                                        && !bi.right.may_have_side_effects()
                                    {
                                        *expr = self.ast.literal_boolean_expression(
                                            self.ast.boolean_literal(bi.span, true),
                                        );
                                    } else {
                                        bi.operator = BinaryOperator::Equality;
                                    }
                                }
                                PrimitiveTypeComparison::NeverSameType | PrimitiveTypeComparison::AlwaysSameTypeNeverSameValue => {
                                    if !bi.left.may_have_side_effects()
                                        && !bi.right.may_have_side_effects()
                                    {
                                        *expr = self.ast.literal_boolean_expression(
                                            self.ast.boolean_literal(bi.span, false),
                                        );
                                    } else {
                                        bi.operator = BinaryOperator::Equality;
                                    }
                                }
                            }
                        }
                        (_, _) => {}
                    }
                }
                _ => {}
            };
        }
    }

    /// Removes redundant argument of `ReturnStatement`
    ///
    /// `return undefined` -> `return`
    /// `return void 0` -> `return`
    fn compress_return_statement(&mut self, stmt: &mut ReturnStatement<'a>) {
        if stmt.argument.as_ref().is_some_and(|expr| expr.is_undefined() || expr.is_void_0()) {
            stmt.argument = None;
        }
    }

    fn compress_variable_declarator(&mut self, decl: &mut VariableDeclarator<'a>) {
        if decl.kind.is_const() {
            return;
        }
        if decl.init.as_ref().is_some_and(|init| init.is_undefined() || init.is_void_0()) {
            decl.init = None;
        }
    }

    /// [Peephole Reorder Constant Expression](https://github.com/google/closure-compiler/blob/master/src/com/google/javascript/jscomp/PeepholeReorderConstantExpression.java)
    ///
    /// Reorder constant expression hoping for a better compression.
    /// ex. x === 0 -> 0 === x
    /// After reordering, expressions like 0 === x and 0 === y may have higher
    /// compression together than their original counterparts.
    #[allow(unused)]
    fn reorder_constant_expression(&self, expr: &mut BinaryExpression<'a>) {
        let operator = expr.operator;
        if operator.is_equality()
            || operator.is_compare()
            || operator == BinaryOperator::Multiplication
        {
            if expr.precedence() == expr.left.precedence() {
                return;
            }
            if !expr.left.is_immutable_value() && expr.right.is_immutable_value() {
                if let Some(inverse_operator) = operator.compare_inverse_operator() {
                    expr.operator = inverse_operator;
                }
                std::mem::swap(&mut expr.left, &mut expr.right);
            }
        }
    }
}

impl<'a> VisitMut<'a> for Compressor<'a> {
    fn visit_statements(&mut self, stmts: &mut Vec<'a, Statement<'a>>) {
        stmts.retain(|stmt| true);

        for stmt in stmts.iter_mut() {
            self.visit_statement(stmt);
        }
    }

    fn visit_statement(&mut self, stmt: &mut Statement<'a>) {
        self.compress_block(stmt);
        // self.fold_condition(stmt);
        self.visit_statement_match(stmt);
    }

    fn visit_return_statement(&mut self, stmt: &mut ReturnStatement<'a>) {
        if let Some(arg) = &mut stmt.argument {
            self.visit_expression(arg);
        }
    }

    fn visit_variable_declaration(&mut self, decl: &mut VariableDeclaration<'a>) {
        for declarator in decl.declarations.iter_mut() {
            self.visit_variable_declarator(declarator);
        }
    }

    fn visit_expression(&mut self, expr: &mut Expression<'a>) {
        self.visit_expression_match(expr);
        self.fold_expression(expr);
        self.compress_overly_strict(expr);
        if !self.compress_undefined(expr) {
            self.compress_boolean(expr);
        }
    }

    fn visit_binary_expression(&mut self, expr: &mut BinaryExpression<'a>) {
        self.visit_expression(&mut expr.left);
        self.visit_expression(&mut expr.right);

        self.compress_typeof_undefined(expr);
    }
}
