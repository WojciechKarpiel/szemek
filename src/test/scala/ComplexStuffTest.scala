package pl.wojciechkarpiel.szemek

import Interval.{Min, One, Zero}
import Term.*
import TypeChecking.V2.{InferResult, eqNormalizingNoCheck}
import TypeChecking.{V2, fullyNormalizeNoCheck}
import core.Face

import org.scalatest.funsuite.AnyFunSuiteLike

class ComplexStuffTest extends AnyFunSuiteLike {

  test("kan reducing for I0 and I1") {
    val a0 = GlobalVar(Id("a0"))
    val aP = GlobalVar(Id("A"))
    val u = GlobalVar(Id("u"))
    val f: Face = Face.OneFace // todo too easy?
    val aTpe: Interval => (Term, System) = i => (PathElimination(aP, i), System(Seq((f, PathElimination(u, i))), PathElimination(aP, i)))

    def kn(i: Interval) = kanFill(a0, aTpe, i)

    val ctx = Context.Empty // todo better example
      .add(aP.id, PathType(_ => Universe, NatType, NatType)) //todo make it diff
      .add(a0.id, TypedTerm(NatZero, PathElimination(aP, Zero)))
      .addChecking(u.id, PathType(i => PathElimination(aP, i), NatZero, Suc(NatZero)))
    // 1. Check tpe of kn in general
    val k = PhI.fresh()
    val arbitraryKan = kn(k)
    V2.checkInferType(arbitraryKan, ctx) match
      case InferResult.Ok(tpe) =>
        assert(eqNormalizingNoCheck(tpe, PathElimination(aP, Min(One, k)))(ctx))
      case InferResult.Fail(msg) => fail(msg)
    // 2. Check reduction of Kan0
    val kan0 = kn(Zero)
    V2.checkInferType(kan0, ctx) match
      case InferResult.Ok(tpe) =>
        assert(eqNormalizingNoCheck(tpe, NatType)(ctx))
        assert(fullyNormalizeNoCheck(kan0, ctx) == NatZero)
      case InferResult.Fail(msg) => fail(msg)
    // 3. Check reduction of Kan1
    val kan1 = kn(One)
    V2.checkInferType(kan1, ctx) match
      case InferResult.Ok(tpe) =>
        assert(eqNormalizingNoCheck(tpe, NatType)(ctx))
        assert(fullyNormalizeNoCheck(kan1, ctx) == Suc(NatZero))
      case InferResult.Fail(msg) => fail(msg)
  }
}
