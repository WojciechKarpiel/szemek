package pl.wojciechkarpiel.szemek
package parser

import Interval.*
import Term.*

import org.parboiled2.ParseError
import org.scalatest.funsuite.AnyFunSuiteLike
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult.Ok
import pl.wojciechkarpiel.szemek.TypeChecking.{checkCtx, fullyNormalize}
import pl.wojciechkarpiel.szemek.parser.NonHoasTerm.Face.{EqOne, EqZero, FaceMax}

import scala.util.{Failure, Success}

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

  def assertFace(in: String, expected: NonHoasTerm.Face): Unit = {
    new CubicalTypeTheoryParser(in).FaceStartForTest.run() match
      case Failure(exception) => throw exception
      case Success(value) => assert(value == expected)
  }

  test("Face parsing - dd") {
    val eq0 = EqZero(NonHoasTerm.Interval.NamedInterval("i"))
    val eq1 = EqOne(NonHoasTerm.Interval.NamedInterval("j"))
    assertFace("Feq0(i)", eq0)
    assertThrows[ParseError](assertFace("Fmax(Feq0(i)", eq0))
    assertFace("Fmax(Feq0(i), Feq1(j))", FaceMax(eq0, eq1))
    assertFace("Fmax(Feq1(I1), Feq0(~max(elo, I0)))", FaceMax(
      EqOne(NonHoasTerm.Interval.One),
      EqZero(NonHoasTerm.Interval.Opp(
        NonHoasTerm.Interval.Max(
          NonHoasTerm.Interval.NamedInterval("elo"),
          NonHoasTerm.Interval.Zero
        )
      ))
    ))
  }

  test("system parse") {
    val in = """[ Feq0(i) -> 0, F1 -> S(0) ]:Nat"""
    assert(CubicalTypeTheoryParser(in).InputLine.run().get.term == NonHoasTerm.SystemTerm(Seq(
      (NonHoasTerm.Face.EqZero(NonHoasTerm.Interval.NamedInterval("i")), NonHoasTerm.NatZeroTerm),
      (NonHoasTerm.Face.OneFace, NonHoasTerm.SucTerm(NonHoasTerm.NatZeroTerm))
    ), NonHoasTerm.NatTypeTerm))
  }

  test("comp parse") {
    // TODO rework to proper full parsing
    val in = """Comp( 0 ,i -> [ Feq0(i) -> 0, F1 -> S(0) ]:Nat)"""
    assert(CubicalTypeTheoryParser(in).InputLine.run().get.term ==
      NonHoasTerm.Composition(NonHoasTerm.NatZeroTerm, "i",
        NonHoasTerm.SystemTerm(Seq(
          (NonHoasTerm.Face.EqZero(NonHoasTerm.Interval.NamedInterval("i")), NonHoasTerm.NatZeroTerm),
          (NonHoasTerm.Face.OneFace, NonHoasTerm.SucTerm(NonHoasTerm.NatZeroTerm))
        ), NonHoasTerm.NatTypeTerm)))
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