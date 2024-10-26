package pl.wojciechkarpiel.szemek
package parser

import org.parboiled2.*
import org.parboiled2.support.hlist.*


class TestGrammar(val input: ParserInput) extends Parser {

  import TestGrammar.Trm
  import TestGrammar.Trm.*

  private def In: Rule1[Trm] = rule {
    TopLevel ~ EOI
  }

  private def TopLevel: Rule1[Trm] = rule {
    oneOrMore((Paren | Identifier) ~ " ".?) ~> ((a: Seq[Trm]) => a.reduce(App.apply))
  }

  private def Paren: Rule1[Trm] = rule {
    "(" ~ TopLevel ~ ")"
  }

  private def AppLeft: Rule[Trm :: HNil, Trm :: HNil] = rule {
    " " ~ TopLevel ~> ((a: Trm, b: Trm) => App(a, b))
  }

  private def Identifier: Rule1[Trm] = rule {
    capture(CharPredicate.Alpha ~ zeroOrMore(CharPredicate.AlphaNum)) ~> ((s: String) => Str(s))
  }
}

/*
E = s
E = E E

 */
object TestGrammar {

  import scala.util.{Failure, Success, Try}

  def mainQ(args: Array[String]): Unit = {
    val parser = new TestGrammar("a b c d")
    val result: Try[Trm] = parser.In.run()
    result match {
      case Success(result) =>
        print(result)
      case Failure(e: ParseError) =>
        print(parser.formatError(e, new ErrorFormatter(showTraces = true)))
      case scala.util.Failure(e) => e.printStackTrace()
    }
  }

  private enum Trm:
    case Str(s: String)
    case App(a: Trm, b: Trm)
}