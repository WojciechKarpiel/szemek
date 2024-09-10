package pl.wojciechkarpiel.szemek

import Term.{Lambda, NatType}

import org.scalatest.funsuite.AnyFunSuiteLike

class TermTest extends AnyFunSuiteLike {

  test("Lambda equality") {
    val x1 = Lambda(NatType, x => Lambda(NatType, y => x))
    val y1 = Lambda(NatType, x => Lambda(NatType, y => y))
    val x2 = Lambda(NatType, x => Lambda(NatType, y => x))
    val y2 = Lambda(NatType, x => Lambda(NatType, y => y))
    assert(x1 == x2)
    assert(y1 == y2)
    assert(x1 != y1)
    assert(x2 != y2)
    assert(x1.hashCode() == x2.hashCode())
    assert(y1.hashCode() == y2.hashCode())


    // sanity check
    assert(!(x1 eq x2))
    assert(!(y1 eq y2))
  }

}
