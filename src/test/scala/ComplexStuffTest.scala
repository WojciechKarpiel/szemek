package pl.wojciechkarpiel.szemek

import org.scalatest.funsuite.AnyFunSuiteLike
import pl.wojciechkarpiel.szemek.Interval.{Min, One, PhantomInterval, Zero}
import pl.wojciechkarpiel.szemek.Term.*
import pl.wojciechkarpiel.szemek.TypeChecking.V2
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult
import pl.wojciechkarpiel.szemek.core.Face

class ComplexStuffTest extends AnyFunSuiteLike {

  test("kan reducing for I0 and I1") {
    val a0 = GlobalVar(Id("a0"))
    val aP = GlobalVar(Id("A"))
    val u = GlobalVar(Id("u"))
    val f: Face = Face.OneFace // todo too easy?
    val aTpe: Interval => (Term, System) = i => (PathElimination(aP, i), System(Seq((f, PathElimination(u, i))), PathElimination(aP, i)))

    def kn(i: Interval) = kanFill(a0, aTpe, i)

    val ctx = Context.Empty
      .add(aP.id, PathType(_ => Universe, NatType, NatType)) //todo make it diff
      .addChecking(a0.id, PathElimination(aP, Zero))
      .addChecking(u.id, PathType(i => PathElimination(aP, i), NatZero, Suc(NatZero))) // todo wron
    // 1. Check tpe of kn in general
    val arbitraryKan = kn(PhI.fresh())
    // TODO
    V2.checkInferType(arbitraryKan, ctx) match
      case InferResult.Ok(tpe) => ???
      case InferResult.Fail(msg) => fail(msg)
    // 2. Check reduction of Kan0
    val kan0 = kn(Zero)
    // TODO
    // 3. Check reduction of Kan1
    val kan1 = kn(One)
    // TODO
  }
}
