package pl.wojciechkarpiel.szemek

import Term.*
import TypeChecking.rewriteRule

import org.scalatest.funsuite.AnyFunSuiteLike

class TypeCheckingTest extends AnyFunSuiteLike {

  test("App normal OK "){
    val lmb = Lambda(NatType, x => Suc(Suc(x)))
    val arg = Suc(NatZero)
    val app = Application(lmb, arg)

    assert(rewriteRule(app, Context.Empty) == Suc(Suc(Suc(NatZero)))
    )
  }

  test("App normal wrong Tpe "){
    val lmb = Lambda(NatZero, x => Suc(Suc(x)))
    val app = Application(lmb, NatZero)
    assertThrows[TypeCheckFailedException](rewriteRule(app, Context.Empty))
  }

  test("Dont fall for depply nested err"){
    val lmb = Lambda(NatType, x => Suc(Suc(x)))
    val arg = Suc(Suc(Suc(Suc(Suc(Suc(Term.NatType))))))
    val app = Application(lmb, arg)

    assertThrows[TypeCheckFailedException](rewriteRule(app, Context.Empty))
  }
}
