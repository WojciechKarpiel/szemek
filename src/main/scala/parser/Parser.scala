package pl.wojciechkarpiel.szemek
package parser

import Term.*

import pl.wojciechkarpiel.szemek.TypeChecking.V2
import pl.wojciechkarpiel.szemek.TypeChecking.V2.{IntervalReplacer, Replacer}
import pl.wojciechkarpiel.szemek.parser.NonHoasTerm.{Face, Interval, TopLevel}
import pl.wojciechkarpiel.szemek.parser.Parser.ParseResultUnchecked

import pl.wojciechkarpiel.szemek.core.{Face => CF}
import pl.wojciechkarpiel.szemek.{Interval => CI}


object Parser {
  final case class ParseResultUnchecked(term: Term, ctx: Context)

  def parse(input: String): ParseResultUnchecked = ParserStarter.parse(input)
}

// TODO MOST THIS CODE AI-GENERATED, VERIFY

//private [parser]
final case class NaiveLocation(start: Int, end: Int)

type Location = NaiveLocation // TODO better loc

private[parser] object NonHoasTerm {

  enum Face:
    case ZeroFace
    case OneFace
    case EqZero(i: Interval)
    case EqOne(i: Interval)
    case FaceMin(f1: Face, f2: Face)
    case FaceMax(f1: Face, f2: Face)
    case NamedFace(name: String)


  enum Interval:
    case Zero
    case One
    case Opp(i: Interval)
    case Min(i1: Interval, i2: Interval)
    case Max(i1: Interval, i2: Interval)
    case NamedInterval(name: String)

  // Adjusted AST for parsing purposes
  sealed trait Term

  final case class MaybeTypedParseTerm(term: Term, tpe: Option[Term]) extends Term

  case class TopLevel(defs: Seq[(String, MaybeTypedParseTerm)], term: Term) extends Term

  case class Parened(term: Term) extends Term {
    override def toString: String = s"($term)"
  }

  //case class System(value: Seq[(Face, Term)], motive: Term, requiresFullRestriction: Boolean = true /*hack to handle composition easier*/) extends Term {
  final case class SystemTerm(value: Seq[(NonHoasTerm.Face, NonHoasTerm.Term)], motive: NonHoasTerm.Term) extends Term

  //case class Composition(a0: Term, typeAndSystem: Interval => (Term, System)) extends Term {
  final case class Composition(a0: NonHoasTerm.Term, iName: String, aTpe: NonHoasTerm.Term, s: NonHoasTerm.Term) extends Term

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

  case class PathAbstractionTerm(varName: String, body: Term, location: NaiveLocation) extends Term {
    override def toString: String = s"λ$varName: $body"
  }

  case class PathEliminationTerm(term: Term, arg: Interval) extends Term {
    override def toString: String = s"PathElimination($term, $arg)"
  }

  case object UniverseTerm extends Term {
    override def toString: String = "Universe"
  }

  case class GlobalVarTerm(name: String) extends Term {
    override def toString: String = name
  }

  case class VariableTerm(name: String, location: NaiveLocation) extends Term {
    override def toString: String = name
  }

  case class NatRecTerm(motive: LambdaTerm, base: Term, step: Term) extends Term {
    override def toString: String = s"NatRec($motive, $base, $step)"
  }
}


private object ParsingAstTransformer {
  final case class Ctx private(term: Map[String, Term], interval: Map[String, CI], shared: Map[String, Term | CI]) {
    def addT(kv: (String, Term)): Ctx = copy(term = term + kv, shared = shared + kv)

    def addI(kv: (String, CI)): Ctx = copy(interval = interval + kv, shared = shared + kv)

    def getT(name: String): Term = term(name)

    def getI(name: String) = interval(name)

    def get(name: String) = shared(name)
  }

  object Ctx {
    val Empty = Ctx(Map.empty, Map.empty, Map.empty)
  }


  private def chaseApplications(curr: NonHoasTerm.Term, sq: Seq[NonHoasTerm.Term]): NonHoasTerm.Term = curr match
    case NonHoasTerm.ApplicationTerm(fun, arg) => chaseApplications(arg, sq :+ fun)
    // todo support path here?
    case other =>
      val s = sq :+ other
      s.reduce(NonHoasTerm.ApplicationTerm.apply)


  // should be done at parsing time but im too retarded
  def fixAppAssociation(term: NonHoasTerm.Term): NonHoasTerm.Term = term match
    case NonHoasTerm.LambdaTerm(varName, argType, body) => NonHoasTerm.LambdaTerm(varName, fixAppAssociation(argType), fixAppAssociation(body))
    case NonHoasTerm.PiTypeTerm(varName, argType, body) => NonHoasTerm.PiTypeTerm(varName, fixAppAssociation(argType), fixAppAssociation(body))
    case a@NonHoasTerm.ApplicationTerm(fun, arg) => chaseApplications(a, Seq())
    //      fixAppAssociation(arg) match
    //        case NonHoasTerm.ApplicationTerm(fun2, arg2) =>
    //          val fnFixd = fixAppAssociation(fun)
    //          NonHoasTerm.ApplicationTerm(NonHoasTerm.ApplicationTerm(fnFixd, (fun2)), (arg2))
    //        case NonHoasTerm.PathEliminationTerm(fun2, arg2) => NonHoasTerm.PathEliminationTerm(NonHoasTerm.ApplicationTerm(fixAppAssociation(fun), (fun2)), (arg2))
    //        case other => NonHoasTerm.ApplicationTerm(fixAppAssociation(fun), other)
    case NonHoasTerm.PathEliminationTerm(term, arg) => NonHoasTerm.PathEliminationTerm(fixAppAssociation(term), arg)
    case NonHoasTerm.PairIntroTerm(fst, snd, sndMotive) => NonHoasTerm.PairIntroTerm(fixAppAssociation(fst), fixAppAssociation(snd), fixAppAssociation(sndMotive))
    case NonHoasTerm.PairTypeTerm(varName, fstType, sndType) => NonHoasTerm.PairTypeTerm(varName, fixAppAssociation(fstType), fixAppAssociation(sndType))
    case NonHoasTerm.FstTerm(pair) => NonHoasTerm.FstTerm(fixAppAssociation(pair))
    case NonHoasTerm.SndTerm(pair) => NonHoasTerm.SndTerm(fixAppAssociation(pair))
    case NonHoasTerm.NatZeroTerm => NonHoasTerm.NatZeroTerm
    case NonHoasTerm.SucTerm(n) => NonHoasTerm.SucTerm(fixAppAssociation(n))
    case NonHoasTerm.NatTypeTerm => NonHoasTerm.NatTypeTerm
    case NonHoasTerm.PathTypeTerm(varName, tpe, start, end) => NonHoasTerm.PathTypeTerm(varName, fixAppAssociation(tpe), fixAppAssociation(start), fixAppAssociation(end))
    case NonHoasTerm.PathAbstractionTerm(varName, body, location) => NonHoasTerm.PathAbstractionTerm(varName, fixAppAssociation(body), location)
    case NonHoasTerm.UniverseTerm => NonHoasTerm.UniverseTerm
    case NonHoasTerm.GlobalVarTerm(name) => NonHoasTerm.GlobalVarTerm(name)
    case NonHoasTerm.VariableTerm(name, location) => NonHoasTerm.VariableTerm(name, location)
    case NonHoasTerm.Parened(value) => NonHoasTerm.Parened(fixAppAssociation(value))
    case NonHoasTerm.NatRecTerm(motive, base, step) => NonHoasTerm.NatRecTerm(fixAppAssociation(motive).asInstanceOf[NonHoasTerm.LambdaTerm], fixAppAssociation(base), fixAppAssociation(step))
    case NonHoasTerm.Composition(a0, nme, aTpe, sys) => NonHoasTerm.Composition(
      fixAppAssociation(a0), nme, fixAppAssociation(aTpe), fixAppAssociation(sys)
    )
    case NonHoasTerm.SystemTerm(value, tpe) => NonHoasTerm.SystemTerm(
      value.map { case (f, t) => (f, fixAppAssociation(t)) }, fixAppAssociation(tpe)
    )
    case NonHoasTerm.TopLevel(defs, term) => NonHoasTerm.TopLevel(defs.map { case (name, term) => (name, NonHoasTerm.MaybeTypedParseTerm(fixAppAssociation(term.term), term.tpe.map(fixAppAssociation))) }, fixAppAssociation(term))

  def transformTopLevel(term: TopLevel, inCtx_ : Ctx): ParseResultUnchecked = {
    var inCtx = inCtx_
    var resultCtx = Context.Empty
    term.defs.foreach { case (name, NonHoasTerm.MaybeTypedParseTerm(term, tpe)) =>
      val t = transform(term, inCtx)
      val tt = transform(tpe.get, inCtx)
      val id = Id(name)
      resultCtx = resultCtx.add(id, TypedTerm(t, tt)) // no check here

      inCtx = inCtx.addT(id.value -> GlobalVar(id))
      (name -> t)
    }

    val term1 = transform(term.term, ctx = inCtx)
    ParseResultUnchecked(term1, resultCtx)
  }

  def transormInterval(i: NonHoasTerm.Interval, ctx: Ctx): CI = {
    def wrk(i: NonHoasTerm.Interval): CI = i match
      case Interval.Zero => CI.Zero
      case Interval.One => CI.One
      case Interval.Opp(i) => CI.Opp(wrk(i))
      case Interval.Min(i1, i2) => CI.Min(wrk(i1), wrk(i2))
      case Interval.Max(i1, i2) => CI.Max(wrk(i1), wrk(i2))
      case Interval.NamedInterval(name) => (ctx.getI(name))

    wrk(i)
  }

  def transormFace(f: NonHoasTerm.Face, ctx: Ctx): CF = {
    def wrk(f: NonHoasTerm.Face): CF = f match
      case Face.ZeroFace => CF.ZeroFace
      case Face.OneFace => CF.OneFace
      case Face.EqZero(i) => CF.EqZero(transormInterval(i, ctx))
      case Face.EqOne(i) => CF.EqOne(transormInterval(i, ctx))
      case Face.FaceMin(f1, f2) => CF.FaceMin(wrk(f1), wrk(f2))
      case Face.FaceMax(f1, f2) => CF.FaceMax(wrk(f1), wrk(f2))
      case Face.NamedFace(name) => ???

    wrk(f)
  }

  def transform(term: NonHoasTerm.Term, ctx: Ctx): Term = term match
    case NonHoasTerm.Parened(t) => transform(t, ctx)
    case NonHoasTerm.SystemTerm(value, motive) =>
      System(
        value.map {
          case (f, t) => transormFace(f, ctx) -> transform(t, ctx)
        },
        transform(motive, ctx)
      )
    case NonHoasTerm.Composition(a0, iNme, aT, sys) =>
      Composition(
        transform(a0, ctx),
        {
          // todo instantiate eagerly
          val intv = PhantomInterval.fresh()
          val newCtx = ctx.addI(iNme, intv)
          val nSys = transform(sys, newCtx).asInstanceOf[System]
          val aTt = transform(aT, newCtx)
          i =>
            (IntervalReplacer(intv, i).apply(aTt),
              IntervalReplacer(intv, i).apply(nSys).asInstanceOf[System])
        }
      )
    case NonHoasTerm.UniverseTerm => Universe
    case NonHoasTerm.FstTerm(pair) => Fst(transform(pair, ctx))
    case NonHoasTerm.SndTerm(pair) => Snd(transform(pair, ctx))
    case NonHoasTerm.GlobalVarTerm(name) => GlobalVar(Id(name))
    case NonHoasTerm.NatZeroTerm => NatZero
    case NonHoasTerm.SucTerm(n) => Suc(transform(n, ctx))
    case NonHoasTerm.NatTypeTerm => NatType
    case NonHoasTerm.LambdaTerm(varName, argType, body) =>
      val argReal = transform(argType, ctx)
      val arg = PhantomVarOfType(argReal)
      val instantiated = transform(body, ctx.addT(varName -> arg)) // force instantiation eagerly
      Lambda(argReal, argR => V2.Replacer(arg, argR).apply(instantiated))
    case NonHoasTerm.PiTypeTerm(varName, argType, body) =>
      PiType(transform(argType, ctx), arg => transform(body, ctx.addT(varName -> arg)))
    case NonHoasTerm.ApplicationTerm(fun, arg) =>
      // tryParseInterval
      tryParseInterval(arg, ctx) match
        case Some(interval) => PathElimination(transform(fun, ctx), interval)
        case None => Application(transform(fun, ctx), transform(arg, ctx))
    //      // tryparsenonitervak
    //      val argq = transform(arg, ctx)
    //      Application(transform(fun, ctx), argq)
    case NonHoasTerm.PairIntroTerm(fst, snd, sndMotive) =>
      PairIntro(transform(fst, ctx), transform(snd, ctx), t => transform(sndMotive, ctx.addT(("_" -> t)))) // TODO pair intro is surely wrong
    case NonHoasTerm.PairTypeTerm(varName, fstType, sndType) =>
      PairType(transform(fstType, ctx), arg => transform(sndType, ctx.addT(varName -> arg)))
    case NonHoasTerm.PathAbstractionTerm(varName, body, loc) =>
      PathAbstraction({ i =>
        transform(body, ctx.addI(varName -> i))
      }, Metadata(loc))
    case NonHoasTerm.PathTypeTerm(varName, tpe, start, end) =>
      PathType(arg => transform(tpe, ctx.addI(varName -> arg)), transform(start, ctx), transform(end, ctx))
    case NonHoasTerm.PathEliminationTerm(term, arg) =>
      PathElimination(transform(term, ctx), transormInterval(arg, ctx))
    case NonHoasTerm.VariableTerm(name, loc) =>
      guess(name, ctx).asInstanceOf[Term]
    case NonHoasTerm.NatRecTerm(motive, base, step) =>
      NatRecursion(
        transform(motive, ctx).asInstanceOf[Lambda].abs, // todo ignores  type and fragile
        transform(base, ctx),
        transform(step, ctx)
      )

  private def guess(name: String, ctx: Ctx): Term | CI =
    ctx.get(name)
  //    val trm = ctxctx.get(name)
  //    val int = pathCtx.get(name)
  //    if trm.nonEmpty && int.nonEmpty then throw new TypeCheckFailedException(s"Variable $name found in both contexts")
  //    if trm.isEmpty && int.isEmpty then throw new TypeCheckFailedException(s"Variable $name not found in context")
  //    if trm.nonEmpty then trm.get else int.get

  private def tryParseInterval(term: NonHoasTerm.Term, ctx: Ctx): Option[CI] = term match
    case NonHoasTerm.VariableTerm(name, _) =>
      ctx.get(name) match
        case i: CI => Some(i)
        case _: Term => None
    case _ => None // TODO
}
