package pl.wojciechkarpiel.szemek
package core

import Term.EigenVal.Constraint
import Term.EigenVal.Constraint.IdenticalTo
import Term.*
import core.EigenEqNoCheck.Result

import org.scalatest.funsuite.AnyFunSuiteLike

class EigenEqNoCheckTest extends AnyFunSuiteLike {

  private def assertEq(a: Term, b: Term, cnstrsAssert: (Seq[Constraint] => Unit) = (d: Seq[Constraint]) => (), ctx: Context = Context.Empty): Unit = {
    val res = EigenEqNoCheck(ctx).equals(a, b)
    res match
      case Result.NonEq => fail(s"$a != $b")
      case Result.IsEq(constr) => cnstrsAssert(constr)
  }

  private def assertNotEq(a: Term, b: Term, ctx: Context = Context.Empty): Unit = {
    val res = EigenEqNoCheck(ctx).equals(a, b)
    assert(res == EigenEqNoCheck.Result.NonEq)
  }

  test("testEquals") {
    assertEq(NatZero, NatZero, c => assert(c == Seq()))
    assertNotEq(NatZero, Suc(NatZero))

    val eigenVal = EigenVal.fresh()
    assertEq(Suc(NatZero), Suc(eigenVal), c => assert(c == Seq(IdenticalTo(NatZero, eigenVal))))
    assertEq(Suc(eigenVal), Suc(NatZero), c => assert(c == Seq(IdenticalTo(eigenVal, NatZero))))
    assertNotEq(NatZero, Suc(eigenVal))
    assertNotEq(Suc(eigenVal), NatZero)


    assertEq(
      Lambda(NatType, x => x),
      Lambda(NatType, x => eigenVal),
      d => {
        assert(d.size == 1)
        assert(d.head.asInstanceOf[IdenticalTo].a.isInstanceOf[PhantomVarOfType])
        assert(d.head.asInstanceOf[IdenticalTo].b == eigenVal)
      }
    )
  }

}
