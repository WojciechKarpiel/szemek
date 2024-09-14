package pl.wojciechkarpiel.szemek

import Interval.Min
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

  test("Dont fall for deeply nested err") {
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

    val oneTimesTwo = fullyNormalize(NatRecApply(times2, Suc(NatZero)), Context.Empty)
    assert(
      oneTimesTwo ==
        Suc(Suc(NatZero))
    )

    assert(
      fullyNormalize(NatRecApply(times2, Suc(Suc(NatZero))), Context.Empty) ==
        Suc(Suc(Suc(Suc(NatZero))))
    )
  }

  test("From paper section 3.2 - first") {
    val a = Term.GlobalVar(Id("a"))
    val A = Term.GlobalVar(Id("A"))
    val b = Term.GlobalVar(Id("b"))
    val B = Term.GlobalVar(Id("B"))
    val f = Term.GlobalVar(Id("f"))
    val p = Term.GlobalVar(Id("p"))
    val ctxBezp = Context.Empty
      .add(A.id, Universe)
      .add(B.id, Universe)
      .add(a.id, A)
      .add(b.id, A)
      .add(f.id, PiType(A, _ => B))
    val ctx = ctxBezp.add(p.id, PathType(_ => A, a, b))
    val term = PathAbstraction(i => Application(f, PathElimination(p, i)))
    val expectedTpe = PathType(_ => B, Application(f, a), Application(f, b))
    val ctxZeZlymB = ctx.add(b.id, B)
    assertThrows[TypeCheckFailedException](inferType(term, ctxBezp))
    assertThrows[TypeCheckFailedException](inferType(term, ctxZeZlymB))
    val inferredNonNormal = inferType(term, ctx)
    val inferredRed = fullyNormalize(inferredNonNormal, ctx)
    assert(inferredRed == expectedTpe)
  }


  test("From paper section 3.2 - second") {
    val A = Term.GlobalVar(Id("A"))
    val B = Term.GlobalVar(Id("B"))
    val f = Term.GlobalVar(Id("f"))
    val g = Term.GlobalVar(Id("g"))
    val p = Term.GlobalVar(Id("p"))
    val ctx = Context.Empty
      .add(A.id, Universe)
      .add(B.id, Universe)
      .add(f.id, PiType(A, _ => B))
      .add(g.id, PiType(A, _ => B))
      .add(p.id, PiType(A, x => PathType(_ => B, Application(f, x), Application(g, x))))
    val term = PathAbstraction(i => Lambda(A,
      x => PathElimination(Application(p, x), i)
    ))
    val expected = PathType(_ => PiType(A, _ => B), f, g)
    val heh = inferType(term, ctx)
    val ans = fullyNormalize(heh, ctx)
    assert(ans == expected)
  }

  test("From paper section 3.2 - third") {
    val a = Term.GlobalVar(Id("a"))
    val A = Term.GlobalVar(Id("A"))
    val b = Term.GlobalVar(Id("b"))
    val B = Term.GlobalVar(Id("B"))
    val p = Term.GlobalVar(Id("p"))
    val ctx = Context.Empty
      .add(A.id, Universe)
      .add(B.id, Universe)
      .add(a.id, A)
      .add(b.id, A)
      .add(p.id, PathType(_ => A, a, b))
    val term = PathAbstraction(i =>
      PairIntro(
        PathElimination(p, i),
        PathAbstraction(j =>
          PathElimination(p, Min(i, j))
        ),
        x => PathType(_ => A, a, x)
      )
    )
    val tpe = inferType(term, ctx)
    val red = fullyNormalize(tpe, ctx)
    val expected = PathType(
      _ => PairType(A, x => PathType(_ => A, a, x)),
      PairIntro(a, PathAbstraction(_ => a), x => PathType(_ => A, a, x)),
      PairIntro(b, p, x => PathType(_ => A, a, x))
    )
    assert(red == expected)
  }
}
