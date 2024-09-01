package pl.wojciechkarpiel.szemek

import Interval.*
import Term.*
import TypeChecking.whfNormalize
import org.scalatest.funsuite.AnyFunSuiteLike

class TypeCheckingTest extends AnyFunSuiteLike {

  test("testWhfNormalize") {
    assert(whfNormalize(PathElimination(PathType(NatType, NatZero, Suc(NatZero)), Zero), Context.Empty) == NatZero)
    assert(whfNormalize(PathElimination(PathType(NatType, NatZero, Suc(NatZero)), One), Context.Empty) == Suc(NatZero))
    assertThrows[TypeCheckFailedException](whfNormalize(PathElimination(PathType(NatType, Term.Pair(NatZero,NatZero), Suc(NatZero)), One), Context.Empty))

  }
}
