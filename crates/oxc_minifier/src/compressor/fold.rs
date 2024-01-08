//! Constant Folding
//!
//! <https://github.com/google/closure-compiler/blob/master/src/com/google/javascript/jscomp/PeepholeFoldConstants.java>

use std::{cmp::Ordering, mem, ops::Not, borrow::{Borrow, Cow}, backtrace::Backtrace};

use num_bigint::BigInt;
#[allow(clippy::wildcard_imports)]
use oxc_ast::ast::*;
use oxc_span::{Atom, GetSpan, Span};
use oxc_syntax::{
    operator::{BinaryOperator, LogicalOperator, UnaryOperator},
    NumberBase,
};

use super::ast_util::{
    get_boolean_value, get_number_value, get_side_free_bigint_value, get_side_free_number_value,
    get_side_free_string_value, get_string_value, is_exact_int64, IsLiteralValue,
    MayHaveSideEffects, NumberValue,
};
use super::Compressor;

/// Tri state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    pub fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Unknown => Self::Unknown,
        }
    }

    pub fn xor(self, other: Self) -> Self {
        self.for_int(-self.value() * other.value())
    }

    pub fn for_int(self, int: i8) -> Self {
        match int {
            -1 => Self::False,
            1 => Self::True,
            _ => Self::Unknown,
        }
    }

    pub fn for_boolean(boolean: bool) -> Self {
        if boolean {
            Self::True
        } else {
            Self::False
        }
    }

    pub fn value(self) -> i8 {
        match self {
            Self::True => 1,
            Self::False => -1,
            Self::Unknown => 0,
        }
    }
}

/// ported from [closure compiler](https://github.com/google/closure-compiler/blob/master/src/com/google/javascript/jscomp/PeepholeFoldConstants.java#L1250)
#[allow(clippy::cast_possible_truncation)]
fn bigint_less_than_number(
    bigint_value: &BigInt,
    number_value: &NumberValue,
    invert: Tri,
    will_negative: bool,
) -> Tri {
    // if invert is false, then the number is on the right in tryAbstractRelationalComparison
    // if it's true, then the number is on the left
    match number_value {
        NumberValue::NaN => Tri::for_boolean(will_negative),
        NumberValue::PositiveInfinity => Tri::True.xor(invert),
        NumberValue::NegativeInfinity => Tri::False.xor(invert),
        NumberValue::Number(num) => {
            if let Some(Ordering::Equal | Ordering::Greater) =
                num.abs().partial_cmp(&2_f64.powi(53))
            {
                Tri::Unknown
            } else {
                let number_as_bigint = BigInt::from(*num as i64);

                match bigint_value.cmp(&number_as_bigint) {
                    Ordering::Less => Tri::True.xor(invert),
                    Ordering::Greater => Tri::False.xor(invert),
                    Ordering::Equal => {
                        if is_exact_int64(*num) {
                            Tri::False
                        } else {
                            Tri::for_boolean(num.is_sign_positive()).xor(invert)
                        }
                    }
                }
            }
        }
    }
}

/// JavaScript Language Type
///
/// <https://tc39.es/ecma262/#sec-ecmascript-language-types>
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ty {
    BigInt,
    Boolean,
    Null,
    Number,
    Object,
    Str,
    Void,
    Undetermined,
}

impl<'a> From<&Expression<'a>> for Ty {
    fn from(expr: &Expression<'a>) -> Self {
        // TODO: complete this
        match expr {
            Expression::BigintLiteral(_) => Self::BigInt,
            Expression::BooleanLiteral(_) => Self::Boolean,
            Expression::NullLiteral(_) => Self::Null,
            Expression::NumberLiteral(_) => Self::Number,
            Expression::StringLiteral(_) => Self::Str,
            Expression::ObjectExpression(_)
            | Expression::ArrayExpression(_)
            | Expression::RegExpLiteral(_)
            | Expression::FunctionExpression(_) => Self::Object,
            Expression::Identifier(ident) => match ident.name.as_str() {
                "undefined" => Self::Void,
                "NaN" | "Infinity" => Self::Number,
                _ => Self::Undetermined,
            },
            Expression::UnaryExpression(unary_expr) => match unary_expr.operator {
                UnaryOperator::Void => Self::Void,
                UnaryOperator::UnaryNegation => {
                    let argument_ty = Self::from(&unary_expr.argument);
                    if argument_ty == Self::BigInt {
                        return Self::BigInt;
                    }
                    Self::Number
                }
                UnaryOperator::UnaryPlus => Self::Number,
                UnaryOperator::LogicalNot => Self::Boolean,
                UnaryOperator::Typeof => Self::Str,
                _ => Self::Undetermined,
            },
            Expression::BinaryExpression(binary_expr) => match binary_expr.operator {
                BinaryOperator::Addition => {
                    let left_ty = Self::from(&binary_expr.left);
                    let right_ty = Self::from(&binary_expr.right);

                    if left_ty == Self::Str || right_ty == Self::Str {
                        return Self::Str;
                    }

                    // There are some pretty weird cases for object types:
                    //   {} + [] === "0"
                    //   [] + {} === "[object Object]"
                    if left_ty == Self::Object || right_ty == Self::Object {
                        return Self::Undetermined;
                    }

                    Self::Undetermined
                }
                _ => Self::Undetermined,
            },
            _ => Self::Undetermined,
        }
    }
}

impl<'a> Compressor<'a> {
    pub(crate) fn fold_expression<'b>(&mut self, expr: &'b mut Expression<'a>) {
        let folded_expr = match expr {
            Expression::BinaryExpression(binary_expr) => match binary_expr.operator {
                // NOTE: string concat folding breaks our current evaluation of Test262 tests. The
                // minifier is tested by comparing output of running the minifier once and twice,
                // respectively. Since Test262Error messages include string concats, the outputs
                // don't match (even though the produced code is valid). Additionally, We'll likely
                // want to add `evaluate` checks for all constant folding, not just additions, but
                // we're adding this here until a decision is made.
                BinaryOperator::Addition if self.options.evaluate => {
                    self.try_fold_addition(binary_expr.span, &binary_expr.left, &binary_expr.right)
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(folded_expr) = folded_expr {
            *expr = folded_expr;
        }
    }

    fn try_fold_addition<'b>(
        &mut self,
        span: Span,
        left: &'b Expression<'a>,
        right: &'b Expression<'a>,
    ) -> Option<Expression<'a>> {
        // skip any potentially dangerous compressions
        if left.may_have_side_effects() || right.may_have_side_effects() {
            return None;
        }

        let left_type = Ty::from(left);
        let right_type = Ty::from(right);
        match (left_type, right_type) {
            (Ty::Undetermined, _) | (_, Ty::Undetermined) => None,

            // string concatenation
            (Ty::Str, _) | (_, Ty::Str) => {
                // no need to use get_side_effect_free_string_value b/c we checked for side effects
                // at the beginning
                let left_string = get_string_value(left)?;
                let right_string = get_string_value(right)?;
                // let value = left_string.to_owned().
                let value = left_string + right_string;
                let string_literal = StringLiteral::new(span, Atom::from(value));
                Some(self.ast.literal_string_expression(string_literal))
            },

            // number addition
            (Ty::Number, _) | (_, Ty::Number)
                // when added, booleans get treated as numbers where `true` is 1 and `false` is 0
                | (Ty::Boolean, Ty::Boolean) => {
                let left_number = get_number_value(left)?;
                let right_number = get_number_value(right)?;
                let Ok(value) = TryInto::<f64>::try_into(left_number + right_number) else { return None };
                // Float if value has a fractional part, otherwise Decimal
                let number_base = if is_exact_int64(value) { NumberBase::Decimal } else { NumberBase::Float };
                let number_literal = self.ast.number_literal(span, value, "", number_base);
                // todo: add raw &str
                Some(self.ast.literal_number_expression(number_literal))
            },
            _ => None
        }
    }

}
