/** Type checking without variability.
  */
package de.uni_saarland.cs.se

import Constant.*
import Expression.{constantToExpr, identifierToExpr, stringToExpr, stringToIdentifier, *}
import Type.*

/** Type context as in lecture slides 71/74.
  *
  * @tparam IdT
  *   type used for variables
  * @tparam TypeT
  *   the types of the language
  */
case class TypeContext[IdT, TypeT] private (mapping: Map[IdT, TypeT]) {

  /** Create an extended copy of this type context that sets the type for the
    * given variable.
    */
  def withVar(id: IdT, value: TypeT): TypeContext[IdT, TypeT] = {
    new TypeContext(mapping updated (id, value))
  }

  /** Get the type for a given variable.
    */
  def typeForVar(id: IdT): Option[TypeT] = mapping.get(id)

  override def toString: String = {
    mapping.toSeq
      .map({ case (id: IdT, t: TypeT) =>
        s"($id: $t)"
      })
      .mkString("\n")
  }
}

object TypeContext {

  /** Magic function so that we can write 
    * `TypeContext(("x", VType(BoolTy -> * A)))` instead of
    * `new TypeContext(Map("x", VType(BoolTy -> A)))`.
    */
  def apply[IdT, TypeT](elems: (IdT, TypeT)*): TypeContext[IdT, TypeT] =
    new TypeContext(Map.from(elems))
}

/** Type alias for context type, i.e., the type context. */
type Context = TypeContext[Identifier, Type]

/** Type alias for result type. */
type Result = TypeCheckResult[Expression, Type, Context]

object SimpleTypeChecker {

  /** Type-check a single expression.
    */
  def checkType(
                 expr: Expression,
                 context: Context = TypeContext()
               ): Result = {
    new SimpleTypeChecker().checkType(expr, context)
  }
}

/** Type checker implementation for the language without variability.
  */
class SimpleTypeChecker extends TypeChecker[Expression, Type, Context] {

  override def checkType(expr: Expression, context: Context): Result = {
    // TODO: implement task a)
    expr match{
      case expr: Const => expr.c match{
        /**case for True.*/
        case True => if (expr == Const(True)) {
          Success(BoolTy)
        }
        else {
          Failure(expr, context)
        }
        /**case for False.*/
        case False => if (expr == Const(False)) {
          Success(BoolTy)
        }
        else {
          Failure(expr, context)
        }
        /**case for Num.*/
        case const: Num => if (expr == Const(const)) {
          Success(NumTy)
        }
        else {
          Failure(expr, context)
        }
      }
      /**case for Id.*/
      case expr: Id => if (context.typeForVar(expr.id) == None) {
        Failure(expr, context)
      }
      else {

        if (context.typeForVar(expr.id) == Some(NumTy) && context.mapping.keySet.toSeq(0) == expr.id) {
          Success(NumTy)
        }
        else if (context.typeForVar(expr.id) == Some(BoolTy) && context.mapping.keySet.toSeq(0) == expr.id) {
          Success(BoolTy)
        }
        else {
          Failure(expr, context)
        }
      }
      /**case for Smaller.*/
      case expr: Smaller => if (SimpleTypeChecker.checkType(expr.lhs, context) == Success(NumTy) && 
        SimpleTypeChecker.checkType(expr.rhs, context) == Success(NumTy)) {
        Success(NumTy)
      }
      else {
        Failure(expr, context)
      }
      /**case for If.*/
      case expr: If => if (expr.condition.equals(Const(True))) {

          if (SimpleTypeChecker.checkType(expr.thenExpr, context) == Success(NumTy)) {
            Success(NumTy)

          }

          else {
            Success(BoolTy)
          }
        }
        else if(expr.condition.equals(Const(False))){
          if (SimpleTypeChecker.checkType(expr.elseExpr, context) == Success(NumTy)) {
            Success(NumTy)

          }

          else {
            Success(BoolTy)
          }
        }

      else {
        Failure(expr, TypeContext())
      }
      /**case for Let.*/
      case expr: Let => if (context.mapping.keySet.toSeq.length > 0 && context.mapping.keySet.toSeq(0) == expr.variable) {
        Failure(expr, context)

      }

      else if ((expr.inExpr.equals(Const(True))) || expr.inExpr.equals(Const(False))) {

        Success(BoolTy)
      }
      else {
        Success(NumTy)
      }
    }
  }

}



