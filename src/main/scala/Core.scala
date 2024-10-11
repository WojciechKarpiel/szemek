package pl.wojciechkarpiel.szemek

import Interval.{One, PhantomInterval, Zero}
import Term.{Counter, PhantomVarOfType}
import core.Face
import core.Face.OneFace


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

    override def toString: String = {
      val phantomVar = PhantomVarOfType.fresh(argType)
      s"λ$phantomVar: $argType => ${abs(phantomVar)}"
    }
  }

  final case class PiType(argType: Term, abs: Term => Term) extends Term with KindOfAbstraction {
    override def abstraction: Abstraction = Abstraction(argType, abs)

    override def toString: String = {
      val phantomVar = PhantomVarOfType.fresh(argType)
      s"Π$phantomVar: $argType => ${abs(phantomVar)}"
    }
  }

  final case class Application(fun: Term, arg: Term) extends Term

  // Sigma type
  final case class PairIntro(fst: Term, snd: Term, sndMotive: Term => Term) extends Term {
    override def hashCode(): Int = Seq(fst, snd, sndMotive(PhantomVarOfType.constant(fst))).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case PairIntro(otherFst, otherSnd, otherSndMotive) =>
          fst == otherFst && snd == otherSnd && {
            val phantomVar = PhantomVarOfType.fresh(fst)
            sndMotive(phantomVar) == otherSndMotive(phantomVar)
          }
        case _ => false
    }

    override def toString: String = {
      val phantomVar = PhantomVarOfType.fresh(fst)
      s"($fst, $snd [${sndMotive(phantomVar)}])"
    }
  }

  final case class PairType(fstTpe: Term, sndTpe: Term => Term) extends Term with KindOfAbstraction {
    override def abstraction: Abstraction = Abstraction(fstTpe, sndTpe)

    override def toString: String = {
      val phantomVar = PhantomVarOfType.fresh(fstTpe)
      s"Σ$phantomVar: $fstTpe => ${sndTpe(phantomVar)}"
    }
  }

  final case class Fst(pair: Term) extends Term

  final case class Snd(pair: Term) extends Term

  // Natural numbers
  object NatZero extends Term {
    override def toString: String = "0"
  }

  final case class Suc(n: Term) extends Term {
    override def toString: String = s"S($n)"
  }

  final case class NatRecursion(motive: Term => Term, forZero: Term, forNext: Term) extends Term

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

    override def toString: String = {
      val i = PhantomInterval.fresh()
      s"Path(${tpe(i)}, $start, $end)"
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

    override def toString: String = {
      val i = PhantomInterval.fresh()
      s"λ$i: ${abs(i)}"
    }
  }

  final case class PathElimination(term: Term, arg: Interval) extends Term

  // U class niv
  object Universe extends Term

  // V class aria
  final case class GlobalVar(id: Id) extends Term

  final case class PhantomVarOfType(tpe: Term, id: Int = Counter.Constant) extends Term {
    override def toString: String = s"P($tpe, $id)"
  }

  object PhantomVarOfType {
    def constant(tpe: Term): PhantomVarOfType = PhantomVarOfType(tpe, Counter.Constant)

    def fresh(tpe: Term): PhantomVarOfType = new PhantomVarOfType(tpe, Counter.next())
  }

  // todo: Add global restrictions to ctx also?
  //  case class Restricted(face: Face) extends Term
  case class System(value: Seq[(Face, Term)], motive: Term) extends Term // todo eq normalize?

  // If Γ, ϕ ` u : A, then Γ ` a : A[ϕ 7→ u] is an abbreviation for Γ ` a : A and Γ, ϕ ` a = u : A.
  case class Composition(trm: Interval => (TypedTerm, System)) extends Term {
    override def hashCode(): Int = trm(PhantomInterval.Constant).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case Composition(otherTrm) =>
          val i = PhantomInterval.fresh()
          trm(i) == otherTrm(i)
        case _ => false
    }

    override def toString: String = {
      val i = PhantomInterval.fresh()
      s"Comp($i, ${trm(i)})"
    }
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

  def fresh(): Interval = {
    val id = Counter.next()
    Interval.PhantomInterval(id)
  }
}


object Interval {
  def normalize(i: Interval): Interval = i match
    case Zero => Zero
    case One => One
    case opp@Interval.Opp(i) => normalize(i) match
      case Zero => One
      case One => Zero
      case _ => opp
    case Min(i1, One) => normalize(i1)
    case Max(i1, Zero) => normalize(i1)
    case min@Min(i1, i2) =>
      val n1 = normalize(i1)
      val n2 = normalize(i2)
      if n1 == n2 then n1 else n1 match
        case Zero => Zero
        case One => n2
        case _ => n2 match
          case Zero => Zero
          case _ => min
    case max@Max(i1, i2) =>
      val n1 = normalize(i1)
      val n2 = normalize(i2)
      if n1 == n2 then n1 else n1 match
        case One => One
        case Zero => n2
        case _ => n2 match
          case One => One
          case _ => max
    case PhantomInterval(id) => PhantomInterval(id)
}

extension (i: Interval)
  def normalize: Interval = Interval.normalize(i)

class TypeCheckFailedException(msg: String = "nie udało się") extends RuntimeException(msg) /*with NoStackTrace*/

// TODO handle restrictions
class Context private(map: Map[Id, TypedTerm], restrictions: Seq[Face] = Seq()) {
  def add(id: Id, term: TypedTerm): Context = new Context(map + (id -> term), restrictions)

  def restricted(f: Face): Context = new Context(map, restrictions :+ f)

  def add(id: Id, tpe: Term): Context = add(id, TypedTerm(PhantomVarOfType.fresh(tpe), tpe))

  def get(id: Id): Option[TypedTerm] = map.get(id)

  def isEmpty: Boolean = map.isEmpty

  def contains(id: Id): Boolean = map.contains(id)
}

object Context {
  val Empty: Context = new Context(Map())
}

final case class TypedTerm(term: Term, tpe: Term)

object TypeChecking {

  import Term.*

  // TODO consider restrictions!!!! maybe separate fn
  //      basically each time you endounter an Interval u need to move
  //      A few guidelines for what happens in case of a specific relation:
  //      - i -> Zero/One => Zero/One
  //      - Opp(i) -> j => j (normalize opp to non-opp
  //      - Phantom(n+m) -> Phantom(n) => Phantom(n) // lower number wind
  /* example: Path (A->B).apply(i) gdzie f:i=0 to A*/
  def rewriteRule(term: Term, ctx: Context): Term = {
    // todo is reweirerule for system  [t1 F1, ..,ti,Fi..]-> `ti` ?
    val res =
      term match
        case app@Term.Application(fun, arg) =>
          rewriteRule(fun, ctx) match
            case Term.Lambda(argType, abs) =>
              // this is supposed to check many things about the lbda
              // TODO: add test which make this check necessary
              if !inferType(fun, ctx).isInstanceOf[PiType] then throw new TypeCheckFailedException()
              if inferType(arg, ctx) == argType then rewriteRule(abs(arg), ctx) else throw new TypeCheckFailedException()
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
            case Term.PairIntro(fst, _, _) =>
              if inferType(pair, ctx).isInstanceOf[PairIntro] then fst else throw new TypeCheckFailedException()
            case _ => proj
        case proj@Term.Snd(pair) =>
          rewriteRule(pair, ctx) match
            case Term.PairIntro(_, snd, _) =>
              if inferType(pair, ctx).isInstanceOf[PairIntro] then snd else throw new TypeCheckFailedException()
            case _ => proj
        case Term.NatRecApply(natRec, nat) =>
          val d@NatRecursion(_, inForZero, inForNext) = rewriteRule(natRec, ctx).asInstanceOf[NatRecursion]
          inferType(d, ctx)
          rewriteRule(nat, ctx) match
            case NatZero => rewriteRule(inForZero, ctx)
            case Suc(n) =>
              rewriteRule(Application(Application(inForNext, nat), NatRecApply(natRec, n)), ctx)
            case _ => throw new TypeCheckFailedException()
        case notRewritable => notRewritable
    val (fin, b) = etaContract(res, ctx)
    if b then rewriteRule(fin, ctx) else fin
  }


  def simplifyCongruences(term: Term, f: Face): Term = {
    def work(term: Term): Term = term match
      case Lambda(argType, abs) => Lambda(work(argType), x => work(abs(x)))
      case PiType(argType, abs) => PiType(work(argType), x => work(abs(x)))
      case Application(fun, arg) => Application(work(fun), work(arg))
      case PairIntro(fst, snd, sndMotive) => PairIntro(work(fst), work(snd), x => work(sndMotive(x)))
      case PairType(fstTpe, sndTpe) => PairType(work(fstTpe), x => work(sndTpe(x)))
      case Fst(pair) => Fst(work(pair))
      case Snd(pair) => Snd(work(pair))
      case Term.NatZero => NatZero
      case Suc(n) => Suc(work(n))
      case NatRecursion(motive, forZero, forNext) => NatRecursion(x => work(motive(x)), work(forZero), work(forNext))
      case NatRecApply(natRec, nat) => NatRecApply(work(natRec), work(nat))
      case Term.NatType => NatType
      case Term.Universe => Universe
      case GlobalVar(id) => GlobalVar(id)
      case PhantomVarOfType(tpe, id) => PhantomVarOfType(work(tpe), id)
      case PathElimination(term, arg) =>
        val i = Face.simplifyCongruences(arg, f)
        PathElimination(work(term), i)
      case PathType(tpe, start, end) =>
        // do we need work after simpltfycong already called?
        PathType(i => work(tpe(Face.simplifyCongruences(i, f))), work(start), work(end))
      case PathAbstraction(abs) =>
        PathAbstraction(i => work(abs(Face.simplifyCongruences(i, f))))
      case System(value, motive) => // not sure if ok
        System(value.map { case (f, t) => (f, work(t)) }, work(motive))

    work(term)
  }

  def inferType(term: Term, ctx: Context): Term = rewriteRule(term, ctx) match {
    case System(pairs_, motive) =>
      val pairs = pairs_.map { case (f, t) => (Face.reduce(f), t) }
      // 1. check if the value is OK
      val faces = pairs.map(_._1)
      if !Face.sufficientlyRestricted(faces) then throw new TypeCheckFailedException()
      // all types with simple restrictions is A
      pairs.foreach { case (f, t) =>
        val t2 = simplifyCongruences(t, f)
        if inferType(t2, ctx) != Universe then throw new TypeCheckFailedException()

        if rewriteRule(t2, ctx) != motive then throw new TypeCheckFailedException()
      }

      pairs.foreach { case (f1, t1) =>
        pairs.foreach { case (f2, t2) =>
          val f = Face.FaceMin(f1, f2)
          val ts1 = simplifyCongruences(t1, f)
          val ts2 = simplifyCongruences(t2, f)
          if ts1 != ts2 then throw new TypeCheckFailedException()
        }
      }

      motive
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
      if inferType(argType, ctx) != Universe then throw new TypeCheckFailedException()
      // 2. Check if body type exsits
      val bodyType = inferType(abs(PhantomVarOfType(argType)), ctx)
      if inferType(bodyType, ctx) != Universe then throw new TypeCheckFailedException()
      PiType(argType, x => inferType(abs(x), ctx))

    case Term.PairType(fstTpe, sndTpe) =>
      if inferType(fstTpe, ctx) != Universe then throw new TypeCheckFailedException()
      if inferType(sndTpe(PhantomVarOfType(fstTpe)), ctx) != Universe then throw new TypeCheckFailedException()
      Universe
    case Term.PairIntro(fst, snd, sndMotive) =>
      val fstTpe = inferType(fst, ctx)
      val sndTpe = inferType(snd, ctx)
      val sndMotivInstance = sndMotive(fst)
      // TODO should be lazy eq instead of full norm
      if sndMotivInstance != fullyNormalize(sndTpe, ctx) then throw new TypeCheckFailedException()
      //      if sndMotivInstance != rewriteRule(sndTpe,ctx) then throw new TypeCheckFailedException()
      PairType(fstTpe, sndMotive)
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
    case Term.NatRecursion(motive, forZero, forN) =>
      val forZeroT = rewriteRule(inferType(forZero, ctx), ctx)
      if forZeroT != rewriteRule(motive(NatZero), ctx) then throw new TypeCheckFailedException()
      val expected = rewriteRule(PiType(NatType, n => PiType(motive(n), _ => motive(Suc(n)))), ctx)
      if rewriteRule(inferType(forN, ctx), ctx) != expected then throw new TypeCheckFailedException()
      motive(PhantomVarOfType.constant(NatType))
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
      inferType(natRec, ctx) match
        case NatRecursion(motive, _, _) =>
          if inferType(nat, ctx) != NatType then throw new TypeCheckFailedException()
          motive(nat)
        case _ => throw new TypeCheckFailedException()
    case Composition(term) =>
      val oned = term(Interval.One)
      // todo checks!
      oned._1.tpe // TODO withing a system? what does it even mean
  }

  private def inferPairType(pairIntro: Term, ctx: Context): PairType = {
    inferType(pairIntro, ctx) match
      case tpe@PairType(a, b) =>
        if inferType(a, ctx) != Universe then throw new TypeCheckFailedException // TODO is this necessary?
        if inferType(b(PhantomVarOfType(a)), ctx) != Universe then throw new TypeCheckFailedException // TODO is this necessary
        tpe
      case _ => throw new TypeCheckFailedException()
  }

  private def etaContract(t: Term, ctx: Context): (Term, Boolean) = t match
    case Lambda(argType, abs) =>
      val phantomVar = PhantomVarOfType.fresh(argType)
      abs(phantomVar) match
        case app@Application(fun, arg) if arg == phantomVar =>
          inferType(argType, ctx)
          inferType(app, ctx)
          (fun, true)
        case _ => (t, false)
    case PathAbstraction(abs) =>
      val i = PhantomInterval.fresh()
      abs(i) match
        case pe@PathElimination(eliminated, arg) if Interval.normalize(arg) == i =>
          inferType(pe, ctx)
          (eliminated, true)
        case _ => (t, false)
    case _ => (t, false)


  // TODO smarter way to tranform ast
  def fullyNormalize(term: Term, ctx: Context): Term = {
    val res = rewriteRule(term, ctx) match
      case System(pairs, motive) =>
        // TODO nornalization should happen within the updated context?
        val k3kd = System(pairs.map { case (f, t) => (Face.reduce(f), fullyNormalize(t, ctx)) }, motive)
        val k3k = rewriteRule(k3kd, ctx)
        k3k match
          case system: System =>
            val d = system.value.find(d => d._1 == OneFace) // what if multiple? shall we verify the overlap?
            d.map(_._2).getOrElse(k3k)
          case _ => k3k

      case c: Composition =>
        val r: Composition = Composition(i => {
          val trm = c.trm(i)
          val (tt, oldsystem) = trm
          val ntt = TypedTerm(fullyNormalize(tt.term, ctx), fullyNormalize(tt.tpe, ctx))
          val nsq = fullyNormalize(oldsystem, ctx)
          nsq match
            case s: System => (ntt, s)
            case notSystem => (ntt, {
              System(Seq((OneFace, notSystem)), inferType(notSystem, ctx))
            })
        });
        val interval = PhantomInterval.fresh()
        val expr = r.trm(interval)
        if expr._2.value.size == 1 && expr._2.value.head._1 == OneFace then {
          // TODO check also if the phantom interval is here, can't do it if it is
          //     or actually not, it's fine
          r.trm(One)._2.value.head._2 // Γ ` compi A [1F 7→ u] a0 = u(i1)
        }
        else r
      case Lambda(argType, abs) => Lambda(fullyNormalize(argType, ctx), x => fullyNormalize(abs(x), ctx))
      case PiType(argType, abs) => PiType(fullyNormalize(argType, ctx), x => fullyNormalize(abs(x), ctx))
      case Application(fun, arg) => Application(fullyNormalize(fun, ctx), fullyNormalize(arg, ctx))
      case PairIntro(fst, snd, sndMotive) => PairIntro(fullyNormalize(fst, ctx), fullyNormalize(snd, ctx), x => fullyNormalize(sndMotive(x), ctx))
      case PairType(fstTpe, sndTpe) => PairType(fullyNormalize(fstTpe, ctx), x => fullyNormalize(sndTpe(x), ctx))
      case Fst(pair) => Fst(fullyNormalize(pair, ctx))
      case Snd(pair) => Snd(fullyNormalize(pair, ctx))
      case Term.NatZero => NatZero
      case Suc(n) => Suc(fullyNormalize(n, ctx))
      case NatRecursion(motive, forZero, forNext) =>
        NatRecursion(x => fullyNormalize(motive(x), ctx), fullyNormalize(forZero, ctx), fullyNormalize(forNext, ctx))
      case NatRecApply(natRec, nat) => NatRecApply(fullyNormalize(natRec, ctx), fullyNormalize(nat, ctx))
      case Term.NatType => NatType
      case PathType(tpe, start, end) => PathType(i => fullyNormalize(tpe(Interval.normalize(i)), ctx), fullyNormalize(start, ctx), fullyNormalize(end, ctx))
      case PathAbstraction(abs) =>
        PathAbstraction(i => fullyNormalize(abs(Interval.normalize(i)), ctx))
      case PathElimination(term, arg) => PathElimination(fullyNormalize(term, ctx), Interval.normalize(arg))
      case Term.Universe => Universe
      case GlobalVar(id) => GlobalVar(id)
      case PhantomVarOfType(tpe, id) => PhantomVarOfType(fullyNormalize(tpe, ctx), id)
    if res == term then
      res
    else
      fullyNormalize(res, ctx) // TODO bad looping, try better
  }
}