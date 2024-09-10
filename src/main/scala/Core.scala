package pl.wojciechkarpiel.szemek

import Interval.{One, PhantomInterval, Zero}
import Term.Counter


final case class Id(value: String) extends AnyVal


// TODO EQ and hashcode for the FN containing types
sealed trait Term

object Term:
  object Counter {
    private var counter: Int = 0

    def next(): Int = {
      counter += 1
      counter
    }

    val Constant: Int = next()
  }

  final case class Abstraction(argType: Term, abs: Term => Term) {
    override def hashCode(): Int =
      Seq(argType, abs(PhantomVarOfType.constant(argType))).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case Abstraction(otherArgType, otherAbs) =>
          argType == otherArgType && {
            val phantomVar = PhantomVarOfType.fresh(argType)
            abs(phantomVar) == otherAbs(phantomVar)
          }
        case _ => false
    }
  }

  trait KindOfAbstraction {
    def abstraction: Abstraction

    override def hashCode(): Int = abstraction.hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case other: KindOfAbstraction => abstraction == other.abstraction
        case _ => false
    }
  }

  // Pi type
  final case class Lambda(argType: Term, abs: Term => Term) extends Term with KindOfAbstraction {
    override def abstraction: Abstraction = Abstraction(argType, abs)
  }

  final case class PiType(argType: Term, abs: Term => Term) extends Term with KindOfAbstraction {
    override def abstraction: Abstraction = Abstraction(argType, abs)
  }

  final case class Application(fun: Term, arg: Term) extends Term

  // Sigma type
  final case class PairIntro(fst: Term, snd: Term) extends Term

  final case class PairType(fstTpe: Term, sndTpe: Term => Term) extends Term with KindOfAbstraction {
    override def abstraction: Abstraction = Abstraction(fstTpe, sndTpe)
  }

  final case class Fst(pair: Term) extends Term

  final case class Snd(pair: Term) extends Term

  // Natural numbers
  object NatZero extends Term

  final case class Suc(n: Term) extends Term

  // Todo this oversimplified
  final case class NatRecursion(forZero: Term, forNext: Term => Term => Term) extends Term

  final case class NatRecApply(natRec: Term, nat: Term) extends Term

  object NatType extends Term

  // P class ath
  final case class PathType(tpe: Interval => Term, start: Term, end: Term) extends Term {
    override def hashCode(): Int = Seq(tpe(PhantomInterval.Constant), start, end).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case PathType(otherTpe, otherStart, otherEnd) =>
          start == otherStart && end == otherEnd && {
            val i = PhantomInterval.fresh()
            tpe(i) == otherTpe(i)
          }
        case _ => false
    }
  }

  final case class PathAbstraction(abs: Interval => Term) extends Term {
    override def hashCode(): Int = abs(PhantomInterval.Constant).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case PathAbstraction(otherAbs) =>
          val i = PhantomInterval.fresh()
          abs(i) == otherAbs(i)
        case _ => false
    }
  }

  final case class PathElimination(term: Term, arg: Interval) extends Term

  // U class niv
  object Universe extends Term

  // V class aria
  final case class GlobalVar(id: Id) extends Term

  final case class PhantomVarOfType(tpe: Term, id: Int = Counter.Constant) extends Term

  object PhantomVarOfType {
    def constant(tpe: Term): PhantomVarOfType = PhantomVarOfType(tpe, Counter.Constant)

    def fresh(tpe: Term): PhantomVarOfType = new PhantomVarOfType(tpe, Counter.next())
  }

enum Interval:
  case Zero
  case One
  case Opp(i: Interval)
  case Min(i1: Interval, i2: Interval)
  case Max(i1: Interval, i2: Interval)
  case PhantomInterval(id: Int)

object PhantomInterval {
  val Constant: Interval = Interval.PhantomInterval(Counter.Constant)

  def fresh(): Interval = Interval.PhantomInterval(Counter.next())
}


object Interval {
  def normalize(i: Interval): Interval = i match
    case Zero => Zero
    case One => One
    case opp@Interval.Opp(i) => normalize(i) match
      case Zero => One
      case One => Zero
      case _ => opp
    case min@Min(i1, i2) =>
      normalize(i1) match
        case Zero => Zero
        case _ => normalize(i2) match
          case Zero => Zero
          case _ => min
    case max@Max(i1, i2) =>
      normalize(i1) match
        case One => One
        case _ => normalize(i2) match
          case One => One
          case _ => max
    case PhantomInterval(id) => PhantomInterval(id)
}

extension (i: Interval)
  def normalize: Interval = Interval.normalize(i)

class TypeCheckFailedException() extends RuntimeException() /*with NoStackTrace*/

class Context private(map: Map[Id, TypedTerm]) {
  def add(id: Id, term: TypedTerm): Context = new Context(map + (id -> term))

  def get(id: Id): Option[TypedTerm] = map.get(id)

  def isEmpty: Boolean = map.isEmpty

  def contains(id: Id): Boolean = map.contains(id)
}

object Context {
  val Empty: Context = new Context(Map())
}

final case class ContextTerm(term: Term, ctx: Context)

final case class Inference(preconditions: Seq[ContextTerm], result: ContextTerm)

final case class EqJudgement(rewriteFrom: Term, rewriteTo: Term, tpe: Term)

final case class TypedTerm(term: Term, tpe: Term)

object TypeChecking {

  import Term.*

  //Well-formed contexts
  def validContext(ctx: Context): Boolean = true

  // Well-formed types

  //  def natTypeInference(ctx: Context):Inference = Inference(Seq(), ContextTerm(NatType, ctx))


  def rewriteRule(term: Term, ctx: Context): Term = {
    term match
      case app@Term.Application(fun, arg) =>
        rewriteRule(fun, ctx) match
          case Term.Lambda(argType, abs) =>
            // this is supposed to check many things about the lbda
            // TODO: add test which make this check necessary
            if !inferType(fun, ctx).isInstanceOf[PiType] then throw new TypeCheckFailedException()
            if inferType(arg, ctx) == argType then abs(arg) else throw new TypeCheckFailedException()
          case _ => app
      case pe@Term.PathElimination(term, arg) =>
        inferType(term, ctx) match
          case pTpe@PathType(_, start, end) =>
            inferType(pTpe, ctx) // in case it's ill-formed
            Interval.normalize(arg) match
              case Interval.Zero => rewriteRule(start, ctx)
              case Interval.One => rewriteRule(end, ctx)
              case inBetween => rewriteRule(term, ctx) match
                case PathAbstraction(abs) => rewriteRule(abs(inBetween), ctx)
                case _ => pe
          case _ => throw new TypeCheckFailedException()
      case proj@Term.Fst(pair) =>
        rewriteRule(pair, ctx) match
          case Term.PairIntro(fst, _) =>
            if inferType(pair, ctx).isInstanceOf[PairIntro] then fst else throw new TypeCheckFailedException()
          case _ => proj
      case proj@Term.Snd(pair) =>
        rewriteRule(pair, ctx) match
          case Term.PairIntro(_, snd) =>
            if inferType(pair, ctx).isInstanceOf[PairIntro] then snd else throw new TypeCheckFailedException()
          case _ => proj
      case Term.NatRecApply(natRec, nat) => {
        val NatRecursion(inForZero, inForNext) = rewriteRule(natRec, ctx).asInstanceOf[NatRecursion]
        // TODO nic nie sprawdza
        rewriteRule(nat, ctx) match
          case NatZero => inForZero
          case Suc(n) => rewriteRule(inForNext(n)(rewriteRule(NatRecApply(natRec, n), ctx)), ctx)
          case _ => throw new TypeCheckFailedException()


      }
      case notRewritable => notRewritable
  }


  def inferType(term: Term, ctx: Context): Term = rewriteRule(term, ctx) match {
    case PhantomVarOfType(tpe, _) => // todo need to check if tpe is tpe?
      if inferType(tpe, ctx) == Universe then tpe else throw new TypeCheckFailedException()
    case Term.Universe => Universe
    case Term.GlobalVar(id) => ctx.get(id).map(_.tpe).getOrElse(throw new TypeCheckFailedException())
    case Term.NatType => Universe
    case Term.NatZero => NatType
    case Term.Suc(n) =>
      if inferType(n, ctx) == NatType then NatType
      else throw new TypeCheckFailedException()
    case Term.Lambda(argType, abs) =>
      // 1. Check that the Arg type is legit
      if inferType(argType, ctx) != Universe then throw new TypeCheckFailedException();
      // 2. Check if body type exsits
      val bodyType = inferType(abs(PhantomVarOfType(argType)), ctx)
      if inferType(bodyType, ctx) != Universe then throw new TypeCheckFailedException();
      PiType(argType, x => inferType(abs(x), ctx))

    case Term.PairType(fstTpe, sndTpe) =>
      if inferType(fstTpe, ctx) != Universe then throw new TypeCheckFailedException()
      if inferType(sndTpe(PhantomVarOfType(fstTpe)), ctx) != Universe then throw new TypeCheckFailedException()
      Universe
    case Term.PairIntro(fst, snd) => // TODO inexact!
      val fstTpe = inferType(fst, ctx)
      val sndTpe = inferType(snd, ctx)
      PairType(fstTpe, _ => sndTpe)
    case Term.PiType(argType, abs) =>
      if inferType(argType, ctx) != Universe then throw new TypeCheckFailedException()
      if inferType(abs(PhantomVarOfType(argType)), ctx) != Universe then throw new TypeCheckFailedException()
      Universe
    case Term.PathType(tpe, start, end) =>
      if inferType(tpe(PhantomInterval.Constant), ctx) != Universe then throw new TypeCheckFailedException()
      if inferType(rewriteRule(start, ctx), ctx) != rewriteRule(tpe(Zero), ctx) then throw new TypeCheckFailedException()
      if inferType(rewriteRule(end, ctx), ctx) != rewriteRule(tpe(One), ctx) then throw new TypeCheckFailedException()
      Universe
    case Term.PathAbstraction(abs) =>
      inferType(abs(PhantomInterval.Constant), ctx)
      PathType(i => inferType(abs(i), ctx), abs(Zero), abs(One))
    case Term.NatRecursion(forZero, forN) => {
      val forZeroT = inferType(forZero, ctx)
      // TODO, do nie stała
      val P = forZeroT
      PiType(NatType, _ => P)
    }
    // has rewrite rules, but is not rewritable
    case Term.Application(fun, arg) =>
      if !inferType(fun, ctx).isInstanceOf[PiType] then throw new TypeCheckFailedException()
      val Term.PiType(argType, abs) = inferType(fun, ctx).asInstanceOf[PiType]
      if inferType(arg, ctx) != argType then throw new TypeCheckFailedException()
      abs(arg)
    case Term.Fst(pair) =>
      inferPairType(pair, ctx).fstTpe
    case Term.Snd(pair) =>
      inferPairType(pair, ctx) match
        case PairType(a, b) => b(PhantomVarOfType(a))
    case Term.PathElimination(term, _) =>
      inferType(term, ctx) match
        case pTpe@PathType(a, _, _) =>
          if inferType(pTpe, ctx) != Universe then throw new TypeCheckFailedException()
          a(PhantomInterval.Constant)
        case _ => throw new TypeCheckFailedException()
    case NatRecApply(natRec: Term, nat: Term) =>
      // TODO, co jak redukowalne
      throw new TypeCheckFailedException()
  }

  private def inferPairType(pairIntro: Term, ctx: Context): PairType = {
    inferType(pairIntro, ctx) match
      case tpe@PairType(a, b) =>
        if inferType(a, ctx) != Universe then throw new TypeCheckFailedException // TODO is this necessary?
        if inferType(b(PhantomVarOfType(a)), ctx) != Universe then throw new TypeCheckFailedException // TODO is this necessary
        tpe
      case _ => throw new TypeCheckFailedException()
  }
}