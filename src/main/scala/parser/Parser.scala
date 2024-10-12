package pl.wojciechkarpiel.szemek
package parser

import org.parboiled2.*
import pl.wojciechkarpiel.szemek.Term.*

import scala.util.{Failure, Success}

// TODO MOST THIS CODE AI-GENERATED, VERIFY

private[parser] object NonHoasTerm {
  // Adjusted AST for parsing purposes
  sealed trait Term

  case class LambdaTerm(varName: String, argType: Term, body: Term) extends Term {
    override def toString: String = s"λ$varName: $argType => $body"
  }

  case class PiTypeTerm(varName: String, argType: Term, body: Term) extends Term {
    override def toString: String = s"Π$varName: $argType => $body"
  }

  case class ApplicationTerm(fun: Term, arg: Term) extends Term {
    override def toString: String = s"($fun $arg)"
  }

  case class PairIntroTerm(fst: Term, snd: Term, sndMotive: Term) extends Term {
    override def toString: String = s"($fst, $snd [$sndMotive])"
  }

  case class PairTypeTerm(varName: String, fstType: Term, sndType: Term) extends Term {
    override def toString: String = s"Σ$varName: $fstType => $sndType"
  }

  case class FstTerm(pair: Term) extends Term {
    override def toString: String = s"Fst($pair)"
  }

  case class SndTerm(pair: Term) extends Term {
    override def toString: String = s"Snd($pair)"
  }

  case object NatZeroTerm extends Term {
    override def toString: String = "0"
  }

  case class SucTerm(n: Term) extends Term {
    override def toString: String = s"S($n)"
  }

  case object NatTypeTerm extends Term {
    override def toString: String = "NatType"
  }

  case class PathTypeTerm(varName: String, tpe: Term, start: Term, end: Term) extends Term {
    override def toString: String = s"Path($varName => $tpe, $start, $end)"
  }

  case class PathAbstractionTerm(varName: String, body: Term) extends Term {
    override def toString: String = s"λ$varName: $body"
  }

  case class PathEliminationTerm(term: Term, arg: Term) extends Term {
    override def toString: String = s"PathElimination($term, $arg)"
  }

  case object UniverseTerm extends Term {
    override def toString: String = "Universe"
  }

  case class GlobalVarTerm(name: String) extends Term {
    override def toString: String = name
  }

  case class VariableTerm(name: String) extends Term {
    override def toString: String = name
  }
}

// Parser implementation
private[parser] class CubicalTypeTheoryParser(val input: ParserInput) extends Parser {

  import NonHoasTerm._

  def InputLine: Rule1[Term] = rule {
    WS ~ Term ~ WS ~ EOI
  }

  def Term: Rule1[Term] = rule {
    LambdaExpr | PiTypeExpr | ApplicationExpr
  }

  def LambdaExpr: Rule1[Term] = rule {
    'λ' ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> ((id: String, argType: Term, body: Term) =>
      LambdaTerm(id, argType, body))
  }

  def PiTypeExpr: Rule1[Term] = rule {
    'Π' ~ WS ~ Identifier ~ WS ~ ':' ~ WS ~ Term ~ WS ~ "=>" ~ WS ~ Term ~> ((id: String, argType: Term, body: Term) =>
      PiTypeTerm(id, argType, body))
  }

  def ApplicationExpr: Rule1[Term] = rule {
    SimpleExpr ~ zeroOrMore(WS ~ SimpleExpr) ~> ((head: Term, tail: Seq[Term]) =>
      tail.foldLeft(head)((acc, arg) => ApplicationTerm(acc, arg)))
  }

  def SimpleExpr: Rule1[Term] = rule {
    NatZeroExpr | SucExpr | NatTypeExpr | UniverseExpr | PairIntroExpr | PairTypeExpr |
      FstExpr | SndExpr | ParensExpr | VariableExpr
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
        val sndMotive = sndMotiveOpt.getOrElse(VariableTerm("_")) // Placeholder if motive is not provided
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

  def ParensExpr: Rule1[Term] = rule {
    '(' ~ WS ~ Term ~ WS ~ ')'
  }

  def VariableExpr: Rule1[Term] = rule {
    Identifier ~> (id => VariableTerm(id))
  }

  def Identifier: Rule1[String] = rule {
    capture(CharPredicate.Alpha ~ zeroOrMore(CharPredicate.AlphaNum))
  }

  def WS: Rule0 = rule {
    quiet(zeroOrMore(anyOf(" \n\r\t\f")))
  }
}

private object ParsingAstTransformer {
  def transform(term: NonHoasTerm.Term, ctx: Map[String, Term]): Term = term match
    case NonHoasTerm.UniverseTerm => Universe
    case NonHoasTerm.FstTerm(pair) => Fst(transform(pair, ctx))
    case NonHoasTerm.SndTerm(pair) => Snd(transform(pair, ctx))
    case NonHoasTerm.GlobalVarTerm(name) => GlobalVar(Id(name))
    case NonHoasTerm.NatZeroTerm => NatZero
    case NonHoasTerm.SucTerm(n) => Suc(transform(n, ctx))
    case NonHoasTerm.NatTypeTerm => NatType
    case NonHoasTerm.LambdaTerm(varName, argType, body) =>
      // TODO force evaluation? instantiate with phantom?
      Lambda(transform(argType, ctx), arg => transform(body, ctx + (varName -> arg)))
    case NonHoasTerm.PiTypeTerm(varName, argType, body) =>
      PiType(transform(argType, ctx), arg => transform(body, ctx + (varName -> arg)))
    case NonHoasTerm.ApplicationTerm(fun, arg) =>
      Application(transform(fun, ctx), transform(arg, ctx))
    case NonHoasTerm.PairIntroTerm(fst, snd, sndMotive) =>
      PairIntro(transform(fst, ctx), transform(snd, ctx), t => transform(sndMotive, ctx + ("_" -> t))) // TODO pair intro is surely wrong
    case NonHoasTerm.PairTypeTerm(varName, fstType, sndType) =>
      PairType(transform(fstType, ctx), arg => transform(sndType, ctx + (varName -> arg)))
    case NonHoasTerm.PathTypeTerm(varName, tpe, start, end) =>
      ???
    //      PathType(arg => transform(tpe,ctx + (varName -> arg)),transform(start,ctx),transform(end,ctx))
    case NonHoasTerm.PathAbstractionTerm(varName, body) => ???
    case NonHoasTerm.PathEliminationTerm(term, arg) => ???
    case NonHoasTerm.VariableTerm(name) => ctx.getOrElse(name, throw new TypeCheckFailedException(s"Variable $name not found in context"))
}


object Parser {

  def parse(input: String): Term =
    val parser = new CubicalTypeTheoryParser(input)

    parser.InputLine.run() match
      case Success(result) =>
        ParsingAstTransformer.transform(result, Map.empty)
      case Failure(e: ParseError) =>
        throw new TypeCheckFailedException(parser.formatError(e))
      case Failure(e) => throw e

}