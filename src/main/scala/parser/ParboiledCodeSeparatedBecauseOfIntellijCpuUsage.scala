package pl.wojciechkarpiel.szemek
package parser

import org.parboiled2.*
import org.parboiled2.support.hlist.*
import pl.wojciechkarpiel.szemek.parser.Parser.ParseResultUnchecked
import pl.wojciechkarpiel.szemek.parser.ParsingAstTransformer.Ctx

import scala.util.{Failure, Success}

// Parser implementation
private[parser] class CubicalTypeTheoryParser(val input: ParserInput) extends Parser {

  import NonHoasTerm.Term
  import NonHoasTerm.Interval
  import NonHoasTerm.*
  import NonHoasTerm.Interval.*

  def InputLine: Rule1[TopLevel] = rule {
    WS ~ zeroOrMore(Def) ~ TopLevelTerm ~ WS ~ EOI ~> ((defs: Seq[(String, MaybeTypedParseTerm)], t: Term) => TopLevel(defs, t))
  }


  def Def: Rule1[(String, MaybeTypedParseTerm)] = rule {
    "def" ~ WS ~ Identifier ~ WS ~ (
      ":" ~ WS ~ Term ~ WS
      ).? ~ ":=" ~ WS ~ Term ~ WS /* ~ "%EOD%" ~ WS*/ ~> ((id: String, tpe: Option[Term], body: Term) => {
      //      println(s"yooo parsed a def $id")
      (id, MaybeTypedParseTerm(body, tpe))
    })
  }


  def Interval: Rule1[NonHoasTerm.Interval] = rule {
    OneInterval | ZeroInterval | OppInterval | MaxInterval | MinInterval | NamedIntervalRule
  }

  private def TopLevelTerm: Rule1[Term] = rule {
    TopLevelTermNoTrailingWs ~ WS
  }

  private def TopLevelTermNoTrailingWs: Rule1[Term] = rule {
    LambdaExprNoTrailingWs | PiTypeExpr | PathAbstractionExprNoTrailingWs | PathTypeExpr |
      NatZeroExpr | SucExpr | NatRecExpr | NatTypeExpr | UniverseExpr | PairIntroExpr | PairTypeExpr |
      FstExpr | SndExpr | ApplicationExpr | ParensExpr | VariableExprNoTrailingWs
  }

  private def ParenedExpr: Rule1[Term] = rule {
    PathAbstractionExprNoTrailingWs ~ WS
  }

  private def ParenedExprNoTrailingWs: Rule1[Term] = rule {
    "(" ~ WS ~ TopLevelTerm ~ WS ~ ")"
  }

  private def TypeTermExpr: Rule1[Term] = rule(TopLevelTerm) // TODO smaller than this

  private def Term: Rule1[Term] = rule(TopLevelTerm) // TODO delet

  private def TermNoTrailingWs: Rule1[Term] = rule(TopLevelTermNoTrailingWs) // TODO delet

  def LambdaExpr: Rule1[Term] = rule {
    LambdaExprNoTrailingWs ~ WS
  }

  def LambdaExprNoTrailingWs: Rule1[Term] = rule {
    ("λ" | "lam" | "fun" | "fn") ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ TermNoTrailingWs ~> ((id: String, argType: Term, body: Term) =>
      LambdaTerm(id, argType, body))
  }

  private def PathTypeExpr: Rule1[Term] = rule {
    "Path" ~ WS ~ PathAbstractionExpr ~ WS ~ Term ~ WS ~ Term ~ WS ~> ((tpe_ : Term, start: Term, end: Term) => {
      val tpe = tpe_.asInstanceOf[PathAbstractionTerm]
      PathTypeTerm(tpe.varName, tpe.body, start, end)
    })
  }

  private def maybeParenedLamExpr: Rule1[Term] = rule {
    ("(" ~ WS ~ LambdaExpr ~ ")" | LambdaExpr) ~ WS
  }

  def PathAbstractionExpr: Rule1[Term] = rule {
    PathAbstractionExprNoTrailingWs ~ WS
  }

  def PathAbstractionExprNoTrailingWs: Rule1[Term] = rule {
    push(cursor) ~ '<' ~ WS ~ Identifier ~ WS ~ '>' ~ WS ~ TermNoTrailingWs ~ push(cursor) ~> ((start: Int, id: String, body: Term, end: Int) =>
      PathAbstractionTerm(id, body, NaiveLocation(start, end)))
  }

  private def NatRecExpr: Rule1[Term] = rule {
    "NatRec" ~ WS ~ maybeParenedLamExpr ~ WS ~ Term ~ WS ~ Term ~> ((motive: Term, base: Term, step: Term) => NatRecTerm(motive.asInstanceOf[LambdaTerm], base, step))
  }

  def PiTypeExpr: Rule1[Term] = rule {
    ("Π" | "Pi") ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> ((id: String, argType: Term, body: Term) =>
      PiTypeTerm(id, argType, body))
  }

  private def AppStartExpr: Rule1[Term] = rule {
    LambdaExprNoTrailingWs | PathAbstractionExprNoTrailingWs | ParenedExprNoTrailingWs | VariableExprNoTrailingWs
  }

  def ApplicationExpr: Rule1[Term] =
    rule {
      AppStartExpr ~ zeroOrMore(" ") ~ (AppEndingExpr | PathEndingExpr)
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
    "S" ~ WS ~ "(" ~ WS ~ Term ~ WS ~ ")" ~> (n => SucTerm(n))
  }

  def NatTypeExpr: Rule1[Term] = rule {
    ("NatType" | "Nat" | "N") ~ WS ~ push(NatTypeTerm)
  }

  def UniverseExpr: Rule1[Term] = rule {
    ("Universe" | "U") ~ WS ~ push(UniverseTerm)
  }

  def PairIntroExpr: Rule1[Term] = rule {
    '(' ~ WS ~ Term ~ WS ~ ',' ~ WS ~ Term ~ WS ~ optional('[' ~ WS ~ Term ~ WS ~ ']') ~ WS ~ ')' ~> (
      (fst: Term, snd: Term, sndMotiveOpt: Option[Term]) => {
        val sndMotive = sndMotiveOpt.getOrElse(VariableTerm("_", ???)) // Placeholder if motive is not provided
        PairIntroTerm(fst, snd, sndMotive)
      })
  }

  def PairTypeExpr: Rule1[Term] = rule {
    ("Σ" | "Sgm" | "Sigma") ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> (
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
    VariableExprNoTrailingWs ~ WS
  }

  private def VariableExprNoTrailingWs: Rule1[Term] = rule {
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


  def FaceStartForTest: Rule1[NonHoasTerm.Face] = rule {
    FaceRule ~ WS ~ EOI
  }

  private def FaceRule: Rule1[NonHoasTerm.Face] = rule {
    ZeroFaceRule | OneFaceRule | EqZeroFaceRule | EqOnwFaceRule | FaceMaxRule | FaceMinRule | NamedFaceRule
  }

  private def ZeroFaceRule: Rule1[NonHoasTerm.Face] = rule("F0" ~ WS ~> (() => NonHoasTerm.Face.ZeroFace))

  private def OneFaceRule: Rule1[NonHoasTerm.Face] = rule("F1" ~ WS ~> (() => NonHoasTerm.Face.OneFace))

  private def NamedFaceRule: Rule1[NonHoasTerm.Face] = rule(Identifier ~ WS ~> ((i: String) => NonHoasTerm.Face.NamedFace(i)))

  // todo postfix
  private def EqZeroFaceRule: Rule1[NonHoasTerm.Face] = rule("Feq0(" ~ WS ~ Interval ~ WS ~ ")" ~ WS ~> ((i: NonHoasTerm.Interval) => NonHoasTerm.Face.EqZero(i)))

  private def EqOnwFaceRule: Rule1[NonHoasTerm.Face] = rule("Feq1(" ~ WS ~ Interval ~ WS ~ ")" ~ WS ~> ((i: NonHoasTerm.Interval) => NonHoasTerm.Face.EqOne(i)))

  // todo infix
  private def FaceMaxRule: Rule1[NonHoasTerm.Face] = rule(
    "Fmax(" ~ WS ~ FaceRule ~ WS ~ "," ~ WS ~ FaceRule ~ WS ~ ")" ~ WS ~> (
      (f1: NonHoasTerm.Face, f2: NonHoasTerm.Face) => NonHoasTerm.Face.FaceMax(f1, f2)
      )
  )

  private def FaceMinRule: Rule1[NonHoasTerm.Face] = rule(
    "Fmin(" ~ WS ~ FaceRule ~ WS ~ "," ~ WS ~ FaceRule ~ WS ~ ")" ~ WS ~> (
      (f1: NonHoasTerm.Face, f2: NonHoasTerm.Face) => NonHoasTerm.Face.FaceMin(f1, f2)
      )
  )
}


private[parser] object ParserStarter {

  def parse(input: ParserInput) = parseQ(input, Map.empty, Map.empty)

  def parseQ(input: ParserInput, ctxt: Map[String, Term], pathCtx: Map[String, Interval]): ParseResultUnchecked =
    val parser = new CubicalTypeTheoryParser(input)

    parser.InputLine.run() match
      case Success(result) =>
        var ctx = Ctx.Empty
        ctxt.foreach((k, v) => ctx = ctx.addT(k, v))
        pathCtx.foreach((k, v) => ctx = ctx.addI(k, v))
        val p = ParsingAstTransformer.fixAppAssociation(result).asInstanceOf[NonHoasTerm.TopLevel]
        val f = ParsingAstTransformer.transformTopLevel(p, ctx)
        f
      case Failure(e: ParseError) =>
        throw sys.error(parser.formatError(e, new ErrorFormatter(showTraces = true)))
      case Failure(e) => throw e

}