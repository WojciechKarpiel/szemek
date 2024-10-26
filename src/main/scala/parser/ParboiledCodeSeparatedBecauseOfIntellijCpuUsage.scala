package pl.wojciechkarpiel.szemek
package parser

import org.parboiled2.*
import org.parboiled2.support.hlist.*
import pl.wojciechkarpiel.szemek.parser.ParsingAstTransformer.Ctx

import scala.util.{Failure, Success}

// Parser implementation
private[parser] class CubicalTypeTheoryParser(val input: ParserInput) extends Parser {

  import NonHoasTerm.Term
  import NonHoasTerm.Interval
  import NonHoasTerm.*
  import NonHoasTerm.Interval.*

  def InputLine: Rule1[NonHoasTerm.Term] = rule {
    WS ~ TopLevelTerm ~ WS ~ EOI
  }

  def Interval: Rule1[NonHoasTerm.Interval] = rule {
    OneInterval | ZeroInterval | OppInterval | MaxInterval | MinInterval | NamedIntervalRule
  }

  private def TopLevelTerm: Rule1[Term] = rule {
    LambdaExpr | PiTypeExpr | PathAbstractionExpr | PathTypeExpr |
      NatZeroExpr | SucExpr | NatTypeExpr | UniverseExpr | PairIntroExpr | PairTypeExpr |
      FstExpr | SndExpr | ApplicationExpr | ParensExpr | VariableExpr
  }

  private def ParenedExpr: Rule1[Term] = rule {
    "(" ~ WS ~ TopLevelTerm ~ WS ~ ")" ~ WS
  }

  private def TypeTermExpr: Rule1[Term] = rule(TopLevelTerm) // TODO smaller than this

  private def Term: Rule1[Term] = rule(TopLevelTerm) // TODO delet

  def LambdaExpr: Rule1[Term] = rule {
    'λ' ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> ((id: String, argType: Term, body: Term) =>
      LambdaTerm(id, argType, body))
  }

  private def PathTypeExpr: Rule1[Term] = rule {
    "Path" ~ WS ~ Identifier ~ WS ~ "->" ~ WS ~ Term ~ WS ~ Term ~ WS ~ Term ~ WS ~> ((varName: String, tpe: Term, start: Term, end: Term) => PathTypeTerm(varName, tpe, start, end))
  }

  def PathAbstractionExpr: Rule1[Term] = rule {
    push(cursor) ~ '<' ~ WS ~ Identifier ~ WS ~ '>' ~ WS ~ Term ~ push(cursor) ~ WS ~> ((start: Int, id: String, body: Term, end: Int) =>
      PathAbstractionTerm(id, body, NaiveLocation(start, end)))
  }

  def PiTypeExpr: Rule1[Term] = rule {
    'Π' ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> ((id: String, argType: Term, body: Term) =>
      PiTypeTerm(id, argType, body))
  }

  private def AppStartExpr: Rule1[Term] = rule {
    LambdaExpr | PathAbstractionExpr | ParenedExpr | VariableExpr
  }

  def ApplicationExpr: Rule1[Term] =
    rule {
      AppStartExpr ~ WS ~ (AppEndingExpr | PathEndingExpr)
    }

  private def PathEndingExpr: Rule[Term :: HNil, Term :: HNil] = rule {
    Interval ~ WS ~> ((head: Term, tail: Interval) =>
      PathEliminationTerm(head, tail))
  }

  private def AppEndingExpr: Rule[Term :: HNil, Term :: HNil] = rule {
    SimpleExpr ~ WS ~> ((head: Term, tail: Term) =>
      ApplicationTerm(head, tail))
  }

  def SimpleExpr: Rule1[Term] = rule {
    TopLevelTerm // TODO
  }

  def NatZeroExpr: Rule1[Term] = rule {
    '0' ~ push(NatZeroTerm)
  }

  def SucExpr: Rule1[Term] = rule {
    "S(" ~ WS ~ Term ~ WS ~ ")" ~> (n => SucTerm(n))
  }

  def NatTypeExpr: Rule1[Term] = rule {
    "NatType" ~ push(NatTypeTerm)
  }

  def UniverseExpr: Rule1[Term] = rule {
    "Universe" ~ push(UniverseTerm)
  }

  def PairIntroExpr: Rule1[Term] = rule {
    '(' ~ WS ~ Term ~ WS ~ ',' ~ WS ~ Term ~ WS ~ optional('[' ~ WS ~ Term ~ WS ~ ']') ~ WS ~ ')' ~> (
      (fst: Term, snd: Term, sndMotiveOpt: Option[Term]) => {
        val sndMotive = sndMotiveOpt.getOrElse(VariableTerm("_", ???)) // Placeholder if motive is not provided
        PairIntroTerm(fst, snd, sndMotive)
      })
  }

  def PairTypeExpr: Rule1[Term] = rule {
    'Σ' ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> (
      (id: String, fstType: Term, sndType: Term) => PairTypeTerm(id, fstType, sndType))
  }

  def FstExpr: Rule1[Term] = rule {
    "Fst(" ~ WS ~ Term ~ WS ~ ")" ~> (pair => FstTerm(pair))
  }

  def SndExpr: Rule1[Term] = rule {
    "Snd(" ~ WS ~ Term ~ WS ~ ")" ~> (pair => SndTerm(pair))
  }

  private def ParensExpr: Rule1[Term] = rule {
    '(' ~ WS ~ Term ~ WS ~ ')' ~> ((t: Term) => NonHoasTerm.Parened(t))
  }

  private def VariableExpr: Rule1[Term] = rule {
    push(cursor) ~ Identifier ~ push(cursor) ~> ((start, id, end) => VariableTerm(id, NaiveLocation(start, end)))
  }

  private def Identifier: Rule1[String] = rule {
    capture(CharPredicate.Alpha ~ zeroOrMore(CharPredicate.AlphaNum))
  }

  private def WS: Rule0 = rule {
    quiet(zeroOrMore(anyOf(" \n\r\t\f")))
  }

  // todo max min infix
  private def MaxInterval: Rule1[NonHoasTerm.Interval] = rule("max" ~ WS ~ "(" ~ WS ~ Interval ~ WS ~ "," ~ WS ~ Interval ~ WS ~ ")" ~ WS ~> ((i1: Interval, i2: Interval) => Max(i1, i2)))

  private def MinInterval: Rule1[NonHoasTerm.Interval] = rule("min" ~ WS ~ "(" ~ WS ~ Interval ~ WS ~ "," ~ WS ~ Interval ~ WS ~ ")" ~ WS ~> ((i1: Interval, i2: Interval) => Min(i1, i2)))

  private def OppInterval: Rule1[NonHoasTerm.Interval] = rule("~" ~ WS ~ Interval ~> ((i: Interval) => Opp(i)))

  private def NamedIntervalRule: Rule1[NonHoasTerm.Interval] = rule(Identifier ~ WS ~> ((i: String) => NamedInterval(i)))

  private def OneInterval: Rule1[NonHoasTerm.Interval] = rule("I1" ~ WS ~> (() => One))

  private def ZeroInterval: Rule1[NonHoasTerm.Interval] = rule("I0" ~ WS ~> (() => Zero))

}


private[parser] object ParserStarter {

  def parse(input: ParserInput) = parseQ(input, Map.empty, Map.empty)

  def parseQ(input: ParserInput, ctxt: Map[String, Term], pathCtx: Map[String, Interval]): Term =
    val parser = new CubicalTypeTheoryParser(input)

    parser.InputLine.run() match
      case Success(result) =>
        var ctx = Ctx.Empty
        ctxt.foreach((k, v) => ctx = ctx.addT(k, v))
        pathCtx.foreach((k, v) => ctx = ctx.addI(k, v))
        ParsingAstTransformer.transform(ParsingAstTransformer.fixAppAssociation(result), ctx)
      case Failure(e: ParseError) =>
        throw sys.error(parser.formatError(e, new ErrorFormatter(showTraces = true)))
      case Failure(e) => throw e

}