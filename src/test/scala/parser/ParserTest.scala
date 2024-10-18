package pl.wojciechkarpiel.szemek
package parser

import Interval.*
import Term.*

import org.scalatest.funsuite.AnyFunSuiteLike

class ParserTest extends AnyFunSuiteLike {

  test("testParse") {
    val res = Parser.parse("λx: NatType => S(x)")
    assert(res == Lambda(NatType, x => Term.Suc(x)))
  }


  test("parse path with loc") {
    val q = Term.GlobalVar(Id("q"))

    val pr = ParserStarter.parseQ("<i> q i", Map("q" -> q), Map.empty)
    assert(pr.isInstanceOf[PathAbstraction])
    val pa = pr.asInstanceOf[PathAbstraction]
    assert(pa == PathAbstraction(i => PathElimination(q, i)))
    assert(pa.metadata.location.start == 0)
    assert(pa.metadata.location.end == 7)
  }

  test("parse app") {
    val q = Term.GlobalVar(Id("q"))
    val pr = ParserStarter.parseQ("λi: NatType => q i", Map("q" -> q), Map.empty)
    assert(pr.isInstanceOf[Lambda])
    val pa = pr.asInstanceOf[Lambda]
    assert(pa == Lambda(NatType, x => Application(q, x)))
  }

  // TODO parse interval with named abstraction
  test("Parse interval") {
    val q = Term.GlobalVar(Id("q"))
    {
      val pr = ParserStarter.parseQ("q ~I1", Map("q" -> q), Map.empty)
      assert(pr == PathElimination(q, Opp(One)))
    }

    {
      val pr = ParserStarter.parseQ("λi: NatType => q ~I1", Map("q" -> q), Map.empty)
      assert(pr.isInstanceOf[Lambda])
      val pa = pr.asInstanceOf[Lambda]
      assert(pa == Lambda(NatType, x => PathElimination(q, Opp(One))))
    }
  }

  // TODO
  test("Nested app - noparens") {
    val q = Term.GlobalVar(Id("q"))
    val x = Term.GlobalVar(Id("x"))
    val y = Term.GlobalVar(Id("y"))
    val ctx = Map("q" -> q, "x" -> x, "y" -> y)
    val parsed = ParserStarter.parseQ("q x y", ctx, Map.empty)
    assert(parsed == Application(Application(q, x), y))
  }
  test("Nested app - parens ") {
    val q = Term.GlobalVar(Id("q"))
    val x = Term.GlobalVar(Id("x"))
    val y = Term.GlobalVar(Id("y"))
    val ctx = Map("q" -> q, "x" -> x, "y" -> y)
    assert(ParserStarter.parseQ("(q x) ", ctx, Map.empty) == Application(q, x))
    assert(ParserStarter.parseQ("(q x) y", ctx, Map.empty) == Application(Application(q, x), y))
    assert(ParserStarter.parseQ("q (x y)", ctx, Map.empty) == Application(q, Application(x, y)))
    assertThrows[RuntimeException](ParserStarter.parseQ("q (x y", ctx, Map.empty))
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