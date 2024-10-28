package pl.wojciechkarpiel.szemek
package parser

import Interval.*
import Term.*

import org.scalatest.funsuite.AnyFunSuiteLike
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult.Ok
import pl.wojciechkarpiel.szemek.TypeChecking.{checkCtx, fullyNormalize}

class ParserTest extends AnyFunSuiteLike {

  test("testParse") {
    val res = Parser.parse("λx: NatType => S(x)").term
    assert(res == Lambda(NatType, x => Term.Suc(x)))
  }


  test("parse path with loc") {
    val q = Term.GlobalVar(Id("q"))

    val pr = ParserStarter.parseQ("<i> q i", Map("q" -> q), Map.empty).term
    assert(pr.isInstanceOf[PathAbstraction])
    val pa = pr.asInstanceOf[PathAbstraction]
    assert(pa == PathAbstraction(i => PathElimination(q, i)))
    assert(pa.metadata.location.start == 0)
    assert(pa.metadata.location.end == 7)
  }

  test("parse app") {
    val q = Term.GlobalVar(Id("q"))
    val pr = ParserStarter.parseQ("λi: NatType => q i", Map("q" -> q), Map.empty).term
    assert(pr.isInstanceOf[Lambda])
    val pa = pr.asInstanceOf[Lambda]
    assert(pa == Lambda(NatType, x => Application(q, x)))
  }

  // TODO parse interval with named abstraction
  test("Parse interval") {
    val q = Term.GlobalVar(Id("q"))
    {
      val pr = ParserStarter.parseQ("q ~I1", Map("q" -> q), Map.empty).term
      assert(pr == PathElimination(q, Opp(One)))
    }

    {
      val pr = ParserStarter.parseQ("λi: NatType => q ~I1", Map("q" -> q), Map.empty).term
      assert(pr.isInstanceOf[Lambda])
      val pa = pr.asInstanceOf[Lambda]
      assert(pa == Lambda(NatType, x => PathElimination(q, Opp(One))))
    }
  }

  test("Nested app - noparens") {
    val q = Term.GlobalVar(Id("q"))
    val x = Term.GlobalVar(Id("x"))
    val y = Term.GlobalVar(Id("y"))
    val z = Term.GlobalVar(Id("z"))
    val ctx = Map("q" -> q, "x" -> x, "y" -> y, "z" -> z)
    assert(ParserStarter.parseQ("q x y z", ctx, Map.empty).term == Application(Application(Application(q, x), y), z))
    assert(ParserStarter.parseQ("q x y", ctx, Map.empty).term == Application(Application(q, x), y))
  }

  test("Nested app - parens ") {
    val q = Term.GlobalVar(Id("q"))
    val x = Term.GlobalVar(Id("x"))
    val y = Term.GlobalVar(Id("y"))
    val z = Term.GlobalVar(Id("z"))
    val ctx = Map("q" -> q, "x" -> x, "y" -> y, "z" -> z)
    assert(ParserStarter.parseQ("(q x) ", ctx, Map.empty).term == Application(q, x))
    assert(ParserStarter.parseQ("(q x) y", ctx, Map.empty).term == Application(Application(q, x), y))
    assert(ParserStarter.parseQ("q (x y)", ctx, Map.empty).term == Application(q, Application(x, y)))
    assert(ParserStarter.parseQ("q (x y) z", ctx, Map.empty).term == Application(Application(q, Application(x, y)), z))
    assertThrows[RuntimeException](ParserStarter.parseQ("q (x y", ctx, Map.empty))
  }


  test("NatRec") {
    val ttwo = "NatRec (lam x:Nat => Nat) 0 (λn: NatType => lam ign:Nat => S(S(n)))"
    //val timesTwo = Parser.parse(ttwo)
    val two = "S(S(0))"

    val validForms = Seq(
      s"(($ttwo) $two)",
      s"($ttwo) $two",
      s"($ttwo) ($two)",
      // these break
      //      s"($ttwo $two)",
      //      s"$ttwo $two",
    )
    val fourNonNorm = Parser.parse(validForms.head).term
    val four = fullyNormalize(fourNonNorm, Context.Empty)
    assert(four == Suc(Suc(Suc(Suc(NatZero)))))

    validForms.foreach(form => {
      val parsed = Parser.parse(form).term
      assert(parsed == fourNonNorm)
    })

  }

  test("defs base- wrong tpe") {
    val in =
      """
        |def x: Nat := S(S(0))
        |def double : Universe := NatRec (lam x:Nat => Nat) 0 (λn: NatType => lam ign:Nat => S(S(n)))
        |
        |(double x)
        |""".stripMargin

    val parsed = Parser.parse(in)
    assertThrows[TypeCheckFailedException](checkCtx(parsed.ctx))
  }

  test("defs base") {
    val in =
      """
        |def x: Nat := S(S(0))
        |def double : Pi x: Nat => Nat := NatRec (lam x:Nat => Nat) 0 (λn: NatType => lam ign:Nat => S(S(n)))
        |
        |(double x)
        |""".stripMargin

    val parsed = Parser.parse(in)
    assert(checkCtx(parsed.ctx).isInstanceOf[Ok])
    assert(fullyNormalize(parsed.term, parsed.ctx) == Suc(Suc(Suc(Suc(NatZero)))))
  }

}

/*
def withLoc[T <: Term](r: => Rule1[T]): Rule1[T] = rule {
  push(cursor) ~ r ~ push(cursor) ~> ((start: Int, term: T, end: Int) => {
    term match {
      case v: VariableTerm     => v.copy(loc = Location(start, end))
      case l: LambdaTerm       => l.copy(loc = Location(start, end))
      case p: PiTypeTerm       => p.copy(loc = Location(start, end))
      case a: ApplicationTerm  => a.copy(loc = Location(start, end))
      // ... Handle other term types
    }
  })
}

  def capturePos[T](r: => Rule1[T]): Rule3[Int, Int, T] = rule {
    push(cursor) ~ r ~ push(cursor)
  }
   */