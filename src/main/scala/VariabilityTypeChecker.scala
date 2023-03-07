/** Type checking with variability.
  */
package de.uni_saarland.cs.se

import Constant.*
import Type.*
import VExpression.*

import cafesat.api.Formulas.Formula
import cafesat.api.{Formulas, Solver}

/** Variability context as in lecture slides 74.
  */
case class VariabilityContext(formula: Formula) {

  /** Make equality consider logical equality of formulas.
    */
  override def equals(obj: Any): Boolean = {
    obj match {
      case other: VariabilityContext =>
        Solver.solveForSatisfiability(!(formula iff other.formula)) match {
          case Some(_) => false
          case None    => true
        }
      case _ => false
    }
  }

  override def toString: String = formula.toString
}

object VariabilityContext {

  /** Creates an empty variability context.
    */
  def emptyContext(): VariabilityContext = new VariabilityContext(Formulas.True)

  /** Allow implicit conversion from formulas to `VariabilityContext`.
    */
  given formulaToVarCtx: Conversion[Formula, VariabilityContext] =
  VariabilityContext(_)
}

/** Type alias for type context type */
type VTypeContext = TypeContext[Identifier, VType]

/** Type alias for context (= variability context + type context) type */
type VContext = (VariabilityContext, VTypeContext)

/** Type alias for result type */
type VResult = TypeCheckResult[VExpression, VType, VContext]

object VariabilityTypeChecker {

  /** Type-check a single expression.
    */
  def checkType(
                 expr: VExpression,
                 context: VContext = createContext()
               ): VResult = {
    new VariabilityTypeChecker().checkType(expr, context)
  }

  /** Simplify creation of variability context + type context.
    */
  def createContext(
                     variabilityContext: VariabilityContext =
                     VariabilityContext.emptyContext(),
                     typeContext: VTypeContext = TypeContext()
                   ): VContext = (variabilityContext, typeContext)
}

/** Type checker implementation for the language with variability.
  */
class VariabilityTypeChecker extends TypeChecker[VExpression, VType, VContext] {

  override def checkType(expr: VExpression, context: VContext): VResult = {
    // TODO: implement task b)

    val sat_solver = Solver.solveForSatisfiability(!(!context._1.formula || Formulas.True))

    expr match {
      /***True***/
      case expr: Const => expr.c match {
        case True => if (expr == Const(True)) {
          Success(VType(BoolTy -> context._1.formula))
        }
        else {
          Failure(expr, context)
        }
        /***False***/
        case False => if (expr == Const(False)) {
          Success(VType(BoolTy -> context._1.formula))
        }
        else {
          Failure(expr, context)
        }
        /***Num***/
        case const: Num => if (expr == Const(const)) {
          Success(VType(NumTy -> context._1.formula))
        }
        else {
          Failure(expr, context)
        }
      }
      /***Id***/
      case expr: Id =>
        val var_type = context._2.typeForVar(expr.id)

        if (context._2.mapping.keySet.exists(_ == expr.id) && sat_solver == None) {
          Success(VType(var_type.get.dom().head -> ((context._1.formula && Formulas.True) || (context._1.formula && Formulas.False))))
        }
        else {
          Failure(expr, context)
        }
      /***Smaller***/
      case expr: Smaller =>
        if (VariabilityTypeChecker.checkType(expr.lhs, context) == Success(VType(Type.NumTy -> Formulas.True)) &&
          VariabilityTypeChecker.checkType(expr.rhs, context) == Success(VType(Type.NumTy -> Formulas.True))) {
          Success(VType(NumTy -> context._1.formula))
        }
        else {
          sat_solver match {

            case None => Failure(expr, context)
          }

        }
      /***If***/
      case expr: If =>

        if (expr.condition.equals(Const(True))) {

          if (VariabilityTypeChecker.checkType(expr.thenExpr, context) == Success(VType(Type.NumTy -> Formulas.True))) {
            Success(VType(NumTy -> context._1.formula))

          }

          else {
            Success(VType(BoolTy -> context._1.formula))
          }
        }
        else if (expr.condition.equals(Const(False))) {
          if (VariabilityTypeChecker.checkType(expr.elseExpr, context) == Success(VType(Type.NumTy -> Formulas.True))) {
            Success(VType(NumTy -> context._1.formula))

          }

          else {
            Success(VType(BoolTy -> context._1.formula))
          }
        }

        else {
          sat_solver match {

            case None => Failure(expr, context)
          }
        }
      /***Let***/
      case expr: Let => if (context._2.mapping.keySet.toSeq.length > 0 && context._2.mapping.keySet.toSeq(0) == expr.variable) {
        sat_solver match {

          case None => Failure(expr, context)
        }

      }

      else if ((expr.inExpr.equals(Const(True))) || expr.inExpr.equals(Const(False))) {

        Success(VType(BoolTy -> context._1.formula))
      }
      else {
        Success(VType(NumTy -> context._1.formula))
      }
      /***Choice***/
      //this is not completely implemented
      case expr: Choice => null
    }
  }


}


