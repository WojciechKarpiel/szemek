package pl.wojciechkarpiel.szemek
package core

import Term.EigenVal.Constraint.IdenticalTo
import Term.EigenVal.Constraints
import TypeChecking.V2.NonCheckingReducer

import pl.wojciechkarpiel.szemek.Term.*
import pl.wojciechkarpiel.szemek.core.EigenEqNoCheck.Result

class EigenEqNoCheck(ctx: Context) {
  def equals(a: Term, b: Term): EigenEqNoCheck.Result = topLevel(a, b)

  private def topLevel(a: Term, b: Term): EigenEqNoCheck.Result = {
    if a == b then EigenEqNoCheck.Result.IsEq(Seq())
    else {
      val t1n = NonCheckingReducer(ctx, unfoldDefinitions = false).whnfNoCheck(a).term
      val t2n = NonCheckingReducer(ctx, unfoldDefinitions = false).whnfNoCheck(b).term
      if t1n == t2n then EigenEqNoCheck.Result.IsEq(Seq())
      else {
        if t1n.isEigenVal || t2n.isEigenVal then
          EigenEqNoCheck.Result.IsEq(Seq(IdenticalTo(t1n, t2n)))
        else eqWhfNoDeltaNoEigen(t1n, t2n)

      }
    }
  }

  private def eqWhfNoDeltaNoEigen(a: Term, b: Term): EigenEqNoCheck.Result = {
    (a, b) match {
      case (NatType, NatType) => EigenEqNoCheck.Result.IsEq(Seq())
      case (_, NatType) | (NatType, _) => EigenEqNoCheck.Result.NonEq
      case (Suc(n1), Suc(n2)) => topLevel(n1, n2)
      case (Suc(_), _) | (_, Suc(_)) => EigenEqNoCheck.Result.NonEq
      case (NatZero, NatZero) => EigenEqNoCheck.Result.IsEq(Seq())
      case (NatZero, _) | (_, NatZero) => EigenEqNoCheck.Result.NonEq
      case (l1@Lambda(t1, f1), l2@Lambda(t2, f2)) => eqAbstraction(l1.abstraction, l2.abstraction)
      case (Lambda(_, _), _) | (_, Lambda(_, _)) => EigenEqNoCheck.Result.NonEq
      case (p1: PiType, p2: PiType) => eqAbstraction(p1.abstraction, p2.abstraction)
      case (PiType(_, _), _) | (_, PiType(_, _)) => EigenEqNoCheck.Result.NonEq
      case (Application(fun1, arg1), Application(fun2, arg2)) =>
        topLevel(fun1, fun2) match
          case Result.NonEq => Result.NonEq
          case Result.IsEq(constr) => topLevel(arg1, arg2) match
            case Result.NonEq => Result.NonEq
            case Result.IsEq(constr2) => Result.IsEq(constr ++ constr2)
      case (Application(_, _), _) | (_, Application(_, _)) => EigenEqNoCheck.Result.NonEq
      // todo remember that defs are not unfolded, unfold if necessary
    }
  }

  private def eqAbstraction(a: Abstraction, b: Abstraction): EigenEqNoCheck.Result = {
    val t1 = a.argType
    val t2 = b.argType
    val f1 = a.abs
    val f2 = b.abs
    topLevel(t1, t2) match {
      case EigenEqNoCheck.Result.NonEq => EigenEqNoCheck.Result.NonEq
      case EigenEqNoCheck.Result.IsEq(constrFromTpe) =>
        val phi = PhantomVarOfType.fresh(t1)
        val inst1 = f1(phi)
        val inst2 = f2(phi)
        topLevel(inst1, inst2) match {
          case EigenEqNoCheck.Result.NonEq => EigenEqNoCheck.Result.NonEq
          case EigenEqNoCheck.Result.IsEq(constrFromInst) => EigenEqNoCheck.Result.IsEq(constrFromTpe ++ constrFromInst)
        }
    }
  }
}

object EigenEqNoCheck {
  enum Result:
    case NonEq
    case IsEq(constr: Constraints)
}