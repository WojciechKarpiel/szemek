package pl.wojciechkarpiel.szemek
package core

import Term.*
import Term.EigenVal.Constraint
import Term.EigenVal.Constraint.IdenticalTo
import core.EigenEqNoCheck.Result

import org.scalatest.funsuite.AnyFunSuiteLike

class EigenEqNoCheckTest extends AnyFunSuiteLike {

  private def assertEq(a: Term, b: Term, cnstrsAssert: (Seq[Constraint] => Unit) = (d: Seq[Constraint]) => (), ctx: Context = Context.Empty): Unit = {
    val res = EigenEqNoCheck(ctx).equals(a, b)
    res match
      case Result.NonEq => fail(s"$a != $b")
      case Result.IsEq(constr) => cnstrsAssert(constr)
  }

  private def assertEqNoConstr(a: Term, b: Term, ctx: Context = Context.Empty): Unit =
    assertEq(a, b, c => assert(c.isEmpty), ctx)

  private def assertNotEq(a: Term, b: Term, ctx: Context = Context.Empty): Unit = {
    val res = EigenEqNoCheck(ctx).equals(a, b)
    assert(res == EigenEqNoCheck.Result.NonEq)
  }

  test("resolves globals if needed") {
    // checks for bug that happened - globals were checked too late in the pattern match and
    val a = GlobalVar(Id("a"))
    val ctx = Context.Empty.add(a.id, TypedTerm(NatZero, NatType))

    assertEqNoConstr(a, NatZero, ctx)
    assertEqNoConstr(TypedTerm(a, NatType), NatZero, ctx)
    assertEqNoConstr(TypedTerm(a, NatType), TypedTerm(NatZero, NatType), ctx)
    assertEqNoConstr(a, TypedTerm(NatZero, NatType), ctx)
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
