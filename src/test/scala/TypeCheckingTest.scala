package pl.wojciechkarpiel.szemek

import Term.*
import TypeChecking.{fullyNormalize, inferType, rewriteRule}

import org.scalatest.funsuite.AnyFunSuiteLike

class TypeCheckingTest extends AnyFunSuiteLike {

  test("App normal OK ") {
    val lmb = Lambda(NatType, x => Suc(Suc(x)))
    val arg = Suc(NatZero)
    val app = Application(lmb, arg)

    assert(rewriteRule(app, Context.Empty) == Suc(Suc(Suc(NatZero)))
    )
  }

  test("App normal wrong Tpe ") {
    val lmb = Lambda(NatZero, x => Suc(Suc(x)))
    val app = Application(lmb, NatZero)
    assertThrows[TypeCheckFailedException](rewriteRule(app, Context.Empty))
  }

  test("Dont fall for depply nested err") {
    val lmb = Lambda(NatType, x => Suc(Suc(x)))
    val arg = Suc(Suc(Suc(Suc(Suc(Suc(Term.NatType))))))
    val app = Application(lmb, arg)

    assertThrows[TypeCheckFailedException](rewriteRule(app, Context.Empty))
  }

  test("Infer path type") {
    val pt0 = inferType(PathAbstraction(_ => NatZero), Context.Empty).asInstanceOf[PathType]
    assert(pt0.start == NatZero)
    assert(pt0.end == NatZero)
    assert(pt0.tpe(PhantomInterval.Constant) == NatType)

    val pa1 = PathAbstraction { i => if i == Interval.Zero then NatZero else Suc(NatZero) }
    assert(rewriteRule(PathElimination(pa1, Interval.Zero), Context.Empty) == NatZero)
    assert(rewriteRule(PathElimination(pa1, Interval.One), Context.Empty) == Suc(NatZero))

    val pt1 = inferType(pa1, Context.Empty).asInstanceOf[PathType]
    assert(pt1.start == NatZero)
    assert(pt1.end == Suc(NatZero))
    assert(pt1.tpe(PhantomInterval.Constant) == NatType)
    assert(pt1 == PathType(_ => NatType, NatZero, Suc(NatZero)))
  }

  test("add") {

    val times2 = NatRecursion(_ => NatType, NatZero,
      //      _ => prev => Suc(Suc(prev))
      Lambda(NatType, _ => Lambda(NatType, prev => Suc(Suc(prev))))
    )

    assert(
      rewriteRule(NatRecApply(times2, NatZero), Context.Empty) ==
        NatZero
    )

    val onetimestwo = fullyNormalize(NatRecApply(times2, Suc(NatZero)), Context.Empty)
    assert(
      onetimestwo ==
        Suc(Suc(NatZero))
    )

    assert(
      fullyNormalize(NatRecApply(times2, Suc(Suc(NatZero))), Context.Empty) ==
        Suc(Suc(Suc(Suc(NatZero))))
    )
  }
}