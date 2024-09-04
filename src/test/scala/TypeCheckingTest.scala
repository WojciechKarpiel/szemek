package pl.wojciechkarpiel.szemek

import Interval.*
import Term.*
import TypeChecking.applyRewriteRules
import org.scalatest.funsuite.AnyFunSuiteLike

class TypeCheckingTest extends AnyFunSuiteLike {

  test("testWhfNormalize") {
    assert(applyRewriteRules(PathElimination(PathType(NatType, NatZero, Suc(NatZero)), Zero), Context.Empty) == NatZero)
    assert(applyRewriteRules(PathElimination(PathType(NatType, NatZero, Suc(NatZero)), One), Context.Empty) == Suc(NatZero))
    assertThrows[TypeCheckFailedException](applyRewriteRules(PathElimination(PathType(NatType, Term.Pair(NatZero,NatZero), Suc(NatZero)), One), Context.Empty))
  }

  test("App normal OK "){
    val lmb = Lambda(NatType, x => Suc(Suc(x)))
    val arg = Suc(NatZero)
    val app = Application(lmb, arg)

    assert(applyRewriteRules(app, Context.Empty) == Suc(Suc(Suc(NatZero)))
    )
  }

  test("App normal wrong Tpe "){
    val lmb = Lambda(NatZero, x => Suc(Suc(x)))
    val app = Application(lmb, NatZero)
    assertThrows[TypeCheckFailedException](applyRewriteRules(app, Context.Empty))
  }

  test("Dont fall for depply nested err"){
    val lmb = Lambda(NatType, x => Suc(Suc(x)))
    val arg = Suc(Suc(Suc(Suc(Suc(Suc(Term.NatType))))))
    val app = Application(lmb, arg)

    assertThrows[TypeCheckFailedException](applyRewriteRules(app, Context.Empty))
  }
}
