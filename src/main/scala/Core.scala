package pl.wojciechkarpiel.szemek

import Interval.{One, PhantomInterval, Zero}
import Term.{Counter, PhantomVarOfType, Universe}
import TypeChecking.V2.{InferResult, NonCheckingReducer, checkInferType}
import core.Face
import core.Face.{IntervalCongruence, OneFace}

import scala.annotation.tailrec


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

  final case class Application(fun: Term, arg: Term) extends Term {
    override def toString: String = s"$fun($arg)"
  }

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

  object NatType extends Term {
    override def toString: String = "ℕ"
  }

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

  final case class PathAbstraction(abs: Interval => Term, metadata: Metadata = Metadata.Empty) extends Term {
    override def hashCode(): Int = abs(PhantomInterval.Constant).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case PathAbstraction(otherAbs, _) =>
          val i = PhantomInterval.fresh()
          abs(i) == otherAbs(i)
        case _ => false
    }

    override def toString: String = {
      val i = PhantomInterval.fresh()
      s"<$i> ${abs(i)}"
    }
  }

  final case class PathElimination(term: Term, arg: Interval) extends Term

  // U class niv
  object Universe extends Term {
    override def toString: String = "|U|"
  }

  // V class aria
  final case class GlobalVar(id: Id) extends Term {
    override def toString: String = id.value
  }

  object GlobalVar {
    def app(id: String): GlobalVar = GlobalVar(Id(id))
  }

  object GV {
    def apply(id: String): GlobalVar = GlobalVar(Id(id))
  }

  final case class PhantomVarOfType(tpe: Term, id: Int = Counter.Constant) extends Term {
    override def toString: String = s"φ$id" // Φφ
  }

  object PhantomVarOfType {
    def constant(tpe: Term): PhantomVarOfType = PhantomVarOfType(tpe, Counter.Constant)

    def fresh(tpe: Term): PhantomVarOfType = new PhantomVarOfType(tpe, Counter.next())
  }

  case class System(value: Seq[(Face, Term)], motive: Term, requiresFullRestriction: Boolean = true /*hack to handle composition easier*/) extends Term {
    override def hashCode(): Int = (value, motive).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case System(otherValue, otherMotive, _) =>
          value == otherValue && motive == otherMotive
        case _ => false
    }
  }

  // If Γ, ϕ ` u : A, then Γ ` a : A[ϕ 7→ u] is an abbreviation for Γ ` a : A and Γ, ϕ ` a = u : A.
  // THERE'S NO i in FACES!!! CHECK THAT faces are i-freee! TODO
  case class Composition(a0: Term, typeAndSystem: Interval => (Term, System)) extends Term {
    override def hashCode(): Int = typeAndSystem(PhantomInterval.Constant).hashCode()

    override def equals(obj: Any): Boolean = obj != null && {
      obj match
        case Composition(othera0, otherTrm) =>
          a0 == othera0 && {
            val i = PhantomInterval.fresh()
            typeAndSystem(i) == otherTrm(i)
          }
        case _ => false
    }

    override def toString: String = {
      val i = PhantomInterval.fresh()
      s"Comp($i, ${typeAndSystem(i)})"
    }
  }

  def kanFill(a0: Term, compR: Interval => (Term, System), i: Interval): Term = Composition(
    a0,
    j =>
      val (trm, sys) = compR(Interval.Min(i, j))
      (trm, sys.copy(value = sys.value ++ Seq((Face.EqZero(i), a0))))
  )

  def transport(A: Interval => Term, a0: Term): Term =
    // empty system shouldn't work bro
    Composition(a0, i => (A(i), System(Seq(), A(i))))

// TODO section 4.5 eq for comp


enum Interval:
  case Zero
  case One
  case Opp(i: Interval)
  case Min(i1: Interval, i2: Interval)
  case Max(i1: Interval, i2: Interval)
  case PhantomInterval(id: Int) // TODO toString better

object PhantomInterval {
  val Constant: Interval = Interval.PhantomInterval(Counter.Constant)

  def fresh(): Interval = {
    val id = Counter.next()
    Interval.PhantomInterval(id)
  }
}

object PhI {
  def fresh(): Interval = PhantomInterval.fresh()
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

class Context private(map: Map[Id, TypedTerm], restrictions: Seq[Face] = Seq()) {
  def add(id: Id, term: TypedTerm): Context = new Context(map + (id -> term), restrictions)

  def restricted(f: Face): Context = new Context(map, restrictions :+ f)

  def add(id: Id, tpe: Term): Context = add(id, TypedTerm(PhantomVarOfType.fresh(tpe), tpe))

  def addChecking(id: Id, tpe: Term): Context = {
    checkInferType(tpe, this) match
      case InferResult.Ok(Universe) =>
        add(id, TypedTerm(PhantomVarOfType.fresh(tpe), tpe))
      case other => throw new TypeCheckFailedException(other.toString)
  }

  def get(id: Id): Option[TypedTerm] = map.get(id)

  def isEmpty: Boolean = map.isEmpty

  def contains(id: Id): Boolean = map.contains(id)

  lazy val intervalCongruence: IntervalCongruence = {
    var face = Face.OneFace
    restrictions.foreach { f => face = Face.FaceMin(face, f) }
    IntervalCongruence.fromFace(face)
  }

  def congruent(i1: Interval, i2: Interval): Boolean = Face.congurentUnderRestriction(i1, i2, intervalCongruence)
  //  def simplifyCongruences(i:Interval):Interval = Face.simplifyCongruences(i, intervalCongruence)
}

object Context {
  val Empty: Context = new Context(Map())
}

final case class TypedTerm(term: Term, tpe: Term)

object TypeChecking {

  import Term.*

  object V2 {
    sealed trait InferResult


    object InferResult {
      def wrapFailure(f: Fail, msg: String): Fail = f.wrap(msg)

      final case class Ok(tpe: Term) extends InferResult

      final case class Fail(msg: String = "nie udalo siw ogarnqt' jytia") extends InferResult {
        def wrap(msg: String): Fail = Fail(s"$msg, spovodovane priez: ${this.msg}")
      }
    }

    import TypeChecking.V2.InferResult.{Fail, Ok}

    final case class ReductionResult(term: Term, equalToInput: Boolean):
      def isChanged: Boolean = !equalToInput

    // TODO better impl

    /** doesn't check if the terma are sound before normalizing */
    def eqNormalizingNoCheck(t1: Term, t2: Term)(ctx: Context): Boolean =
      ctx.intervalCongruence.exFalsoQuodlibet || {
        val t1n = NonCheckingReducer(ctx).whnfNoCheck(t1).term
        val t2n = NonCheckingReducer(ctx).whnfNoCheck(t2).term
        t1n == t2n || {
          t1n match
            case PathType(tpe1, start1, end1) =>
              t2n match
                case PathType(tpe2, start2, end2) =>
                  val i = PhantomInterval.fresh()
                  eqNormalizingNoCheck(tpe1(i), tpe2(i))(ctx) &&
                    eqNormalizingNoCheck(start1, start2)(ctx) &&
                    eqNormalizingNoCheck(end1, end2)(ctx)
                case _ => false
            case PathElimination(term1, arg1) =>
              t2n match
                case PathElimination(term2, arg2) =>
                  ctx.congruent(arg1, arg2) && eqNormalizingNoCheck(term1, term2)(ctx) //then true
                // or else the terms are totally ignored
                //                eqNormalizingNoCheck(term1, term2)(ctx) && {
                //                  Interval.normalize(arg1N) == Interval.normalize(arg2N)
                //                }
                case _ => false
            case _ => false
        }
      }

    private class NonIntrospectingIntervalReplacer(existsNow: Interval, shouldExist: Interval) {
      def apply(term: Term): Term = term match
        // TODO should we reduce context by first explicitly substituting outside?
        case Lambda(argType, abs) => Lambda(apply(argType), x => apply(abs(x)))
        case PiType(argType, abs) => PiType(apply(argType), x => apply(abs(x)))
        case Application(fun, arg) => Application(apply(fun), apply(arg))
        case PairIntro(fst, snd, sndMotive) => PairIntro(apply(fst), apply(snd), x => apply(sndMotive(x)))
        case PairType(fstTpe, sndTpe) =>
          PairType(apply(fstTpe), x => apply(sndTpe(x)))
        case Fst(pair) => Fst(apply(pair))
        case Snd(pair) => Snd(apply(pair))
        case Term.NatZero => NatZero
        case Suc(n) => Suc(apply(n))
        case NatRecursion(motive, forZero, forNext) => NatRecursion(x => apply(motive(x)), apply(forZero), apply(forNext))
        case NatRecApply(natRec, nat) => NatRecApply(apply(natRec), apply(nat))
        case Term.NatType => NatType
        case PathType(tpe, start, end) =>
          PathType(i => apply(tpe(i)), apply(start), apply(end))
        case PathAbstraction(abs, metadata) => PathAbstraction(i => apply(abs(i)), metadata)
        case PathElimination(term, arg) => // note that we're not introspecting the nature of arg
          PathElimination(apply(term), if arg == existsNow then shouldExist else arg)
        case Term.Universe => Universe
        case GlobalVar(id) => GlobalVar(id)
        case p@PhantomVarOfType(_, _) => p
        case System(value, motive, _) => ???
        case Composition(a0, typeAnSystem) => ???
    }

    private class Replacer(existsNow: PhantomVarOfType, shouldExist: Term) {
      def apply(term: Term): Term = term match
        case Lambda(argType, abs) => ???
        case PiType(argType, abs) => PiType(apply(argType), x => apply(abs(x)))
        case Application(fun, arg) => ???
        case PairIntro(fst, snd, sndMotive) => ???
        case PairType(fstTpe, sndTpe) => ???
        case Fst(pair) => ???
        case Snd(pair) => ???
        case Term.NatZero => ???
        case Suc(n) => ???
        case NatRecursion(motive, forZero, forNext) => ???
        case NatRecApply(natRec, nat) => ???
        case Term.NatType => NatType
        case PathType(tpe, start, end) => ???
        case PathAbstraction(abs, metadata) => ???
        case PathElimination(term, arg) => ???
        case Term.Universe => ???
        case g: GlobalVar => g
        case p: PhantomVarOfType => if p == existsNow then shouldExist else p
        case System(value, motive, _) => ???
        case Composition(a0, typeAndSystem) => ???
    }

    class NonCheckingReducer(ctx: Context) {
      def etaContractNoCheck(t: Term): ReductionResult = {
        def unchanged = ReductionResult(t, true)

        def changed(t: Term) = ReductionResult(t, false)

        t match {
          case Lambda(argType, abs) =>
            val phantomVar = PhantomVarOfType.fresh(argType)
            whnfNoCheck(abs(phantomVar)).term match
              case Application(fun, arg) if arg == phantomVar =>
                changed(fun)
              case _ => unchanged
          case PathAbstraction(abs, metadata) =>
            val i = PhantomInterval.fresh()
            whnfNoCheck(abs(i)).term match
              case PathElimination(eliminated, arg) if Interval.normalize(arg) == i =>
                changed(eliminated)
              case _ => unchanged
          case _ => unchanged
        }
      }

      private def rewriteRuleStep(term: Term): ReductionResult = {
        def unchanged = ReductionResult(term, true)

        def changed(t: Term) = ReductionResult(t, false)

        term match
          case GlobalVar(id) => ctx.get(id) match
            case Some(TypedTerm(t, _)) if !(t.isInstanceOf[PhantomVarOfType]) =>
              changed(t) // todo what if this is too eager?
            case _ => unchanged
          case NatRecApply(natRec, nat) =>
            whnfNoCheck(natRec) match
              case ReductionResult(nrec@NatRecursion(_, forZero, forNext), _) =>
                whnfNoCheck(nat) match
                  case ReductionResult(NatZero, _) => changed(forZero)
                  case ReductionResult(suc@Suc(n), _) => changed(Application(Application(forNext, suc), NatRecApply(nrec, n)))
                  case _ => unchanged
              case _ => unchanged
          case Fst(pair) =>
            whnfNoCheck(pair) match
              case ReductionResult(PairIntro(fst, _, _), _) => changed(fst)
              case _ => unchanged
          case Snd(pair) =>
            whnfNoCheck(pair) match
              case ReductionResult(PairIntro(_, snd, _), _) => changed(snd)
              case _ => unchanged
          case Application(fun, arg) =>
            whnfNoCheck(fun) match
              case ReductionResult(Lambda(_, abs), _) => changed(abs(arg))
              case _ => unchanged
          case c: Composition =>
            c.typeAndSystem(One)._2.value.find(f => Face.reduce(f._1) == OneFace) match
              case Some((_, term)) => changed(term)
              case None => unchanged
          case PathElimination(path, arg) =>
            var iNorm = Interval.normalize(arg)
            if ctx.congruent(Zero, iNorm) then iNorm = Zero
            if ctx.congruent(One, iNorm) then iNorm = One
            if ctx.congruent(Zero, iNorm) && ctx.congruent(One, iNorm) then throw new TypeCheckFailedException()
            iNorm match
              case i@(One | Zero) =>
                // todo avoid re-checking, just fetch type
                NonReducingCheckerInferrer(ctx, skipChecksOnlyInfer = true).checkInferType(path) match
                  case Ok(PathType(_, start, end)) =>
                    changed(if i == Zero then start else end)
                  case _ => throw new TypeCheckFailedException() // should not happen
              case _ => unchanged
          case System(sys, _, _) =>
            sys.find { case (f, _) => Face.reduce(f) == OneFace } match
              case Some((_, term)) => changed(term)
              case None => unchanged
          case _ => unchanged
      }

      private def reduceStep(term: Term): ReductionResult =
        val etaContracted = etaContractNoCheck(term)
        if etaContracted.equalToInput
        then rewriteRuleStep(term) else etaContracted

      @tailrec
      final def whnfNoCheck(term: Term): ReductionResult = {
        val reduced = reduceStep(term)
        if reduced.equalToInput then reduced else whnfNoCheck(reduced.term)
      }

      final def fullyNormalizedNoCheck(term: Term): Term = whnfNoCheck(term).term match
        case Lambda(argType, abs) => Lambda(fullyNormalizedNoCheck(argType), x => fullyNormalizedNoCheck(abs(x)))
        case PiType(argType, abs) => PiType(fullyNormalizedNoCheck(argType), x => fullyNormalizedNoCheck(abs(x)))
        case Application(fun, arg) => Application(fullyNormalizedNoCheck(fun), fullyNormalizedNoCheck(arg))
        case PairIntro(fst, snd, sndMotive) => PairIntro(fullyNormalizedNoCheck(fst), fullyNormalizedNoCheck(snd), x => fullyNormalizedNoCheck(sndMotive(x)))
        case PairType(fstTpe, sndTpe) => PairType(fullyNormalizedNoCheck(fstTpe), x => fullyNormalizedNoCheck(sndTpe(x)))
        case Fst(pair) => Fst(fullyNormalizedNoCheck(pair))
        case Snd(pair) => Snd(fullyNormalizedNoCheck(pair))
        case Term.NatZero => NatZero
        case Suc(n) => Suc(fullyNormalizedNoCheck(n))
        case NatRecursion(motive, forZero, forNext) => NatRecursion(x => fullyNormalizedNoCheck(motive(x)), fullyNormalizedNoCheck(forZero), fullyNormalizedNoCheck(forNext))
        case NatRecApply(natRec, nat) => NatRecApply(fullyNormalizedNoCheck(natRec), fullyNormalizedNoCheck(nat))
        case Term.NatType => NatType
        case PathType(tpe, start, end) => PathType(i => fullyNormalizedNoCheck(tpe(i)), fullyNormalizedNoCheck(start), fullyNormalizedNoCheck(end))
        case PathAbstraction(abs, metadata) => PathAbstraction(i => fullyNormalizedNoCheck(abs(i)), metadata)
        case PathElimination(term, arg) => PathElimination(fullyNormalizedNoCheck(term), arg)
        case Term.Universe => Universe
        case GlobalVar(id) => GlobalVar(id)
        case PhantomVarOfType(tpe, id) => PhantomVarOfType(fullyNormalizedNoCheck(tpe), id)
        case c: Composition => c
        case s: System => s
    }

    def checkInferType(term: Term, ctx: Context = Context.Empty): InferResult =
      NonReducingCheckerInferrer(ctx).checkInferType(term)

    class NonReducingCheckerInferrer(ctx: Context, skipChecksOnlyInfer: Boolean = false) {
      /**
       * Checks inferrence correctness.
       * Does not rewrite eagerly
       */
      def checkInferType(term: Term): InferResult = term match
        case Term.NatZero => Ok(NatType)
        case Suc(n) => if checkInferType(n) == Ok(NatType) then Ok(NatType) else Fail()
        case GlobalVar(id) => ctx.get(id).map(t => Ok(t.tpe)).getOrElse(Fail(s"variable $id not found"))
        case Lambda(argType, abs) =>
          if checkInferType(argType) != Ok(Universe) then Fail()
          else {
            val arg = PhantomVarOfType.fresh(argType)
            val bodyInstantiated = abs(arg)
            checkInferType(bodyInstantiated) match
              case InferResult.Ok(bodyType) =>
                Ok(PiType(argType, x => Replacer(arg, x).apply(bodyType)))
              case f: InferResult.Fail => f
          }
        case PiType(argType, abs) =>
          if checkInferType(argType) != Ok(Universe) then Fail()
          else {
            val arg = PhantomVarOfType.fresh(argType)
            val bodyInstantiated = abs(arg)
            if checkInferType(bodyInstantiated) != Ok(Universe) then Fail()
            else Ok(Universe)
          }
        case Application(fun, arg) =>
          checkInferType(fun) match
            case InferResult.Ok(PiType(argType, abs)) =>
              checkInferType(arg) match
                case InferResult.Ok(inferredArgType) =>
                  if eqNormalizingNoCheck(inferredArgType, argType)(ctx) then Ok(abs(arg))
                  else Fail()
                case f: InferResult.Fail => f
            case InferResult.Ok(_) => Fail()
            case f: InferResult.Fail => f
        case PairIntro(fst, snd, sndMotive) =>
          checkInferType(fst) match
            case InferResult.Ok(fstType) =>
              checkInferType(snd) match
                case InferResult.Ok(sndType) =>
                  // Check if the motive itself is sound
                  val x = PhantomVarOfType.fresh(fstType)
                  val generalMotive = sndMotive(x)
                  checkInferType(generalMotive) match
                    case InferResult.Ok(_) => // don't care about particular value, just checking
                      val expected = sndMotive(fst)
                      if eqNormalizingNoCheck(sndType, expected)(ctx)
                      then Ok(PairType(fstType, sndMotive))
                      else Fail(s"Path intro: Provided _._2's type and motive are different:\n$sndType\n$expected")
                    case f: Fail => InferResult.wrapFailure(f, "motive is wrong")
                case f: InferResult.Fail => f
            case f: InferResult.Fail => f
        case PairType(fstTpe, sndTpe) =>
          checkInferType(fstTpe) match
            case InferResult.Ok(Universe) =>
              checkInferType(sndTpe(PhantomVarOfType(fstTpe))) match
                case Ok(Universe) => Ok(Universe)
                case Ok(other) => Fail(s"expected universe, got $other")
                case f: Fail => InferResult.wrapFailure(f, "not a valid type to be type of Snd in pair")
            case Ok(other) => Fail(s"expected universe, got $other")
            case f: Fail => InferResult.wrapFailure(f, "not a valid type to be type of Fst in pair")
        case Fst(pair) =>
          checkInferType(pair) match
            case Ok(PairType(a, _)) => Ok(a)
            case Ok(other) => Fail(s"expected pair, got $other")
            case f: Fail => f.wrap("how can i take fst of this")
        case Snd(pair) =>
          checkInferType(pair) match
            case Ok(PairType(_, sndtpe)) =>
              NonCheckingReducer(ctx).whnfNoCheck(pair).term match
                case PairIntro(fst, _, _) => Ok(sndtpe(fst))
                case other => Fail(s"cannot know second typeif no fst value: $other")
            case Ok(other) => Fail(s"expected pair, got $other")
            case f: Fail => f.wrap("how can i take snd of this")
        case NatRecursion(motive, forZero, forNext) =>
          // Check that motive is a legit type
          val x = PhantomVarOfType.fresh(NatType)
          val instantiatedMotive = motive(x)
          checkInferType(instantiatedMotive) match
            case InferResult.Ok(Universe) =>
              checkInferType(forZero) match
                case Ok(forZeroTpe) =>
                  eqNormalizingNoCheck(forZeroTpe, motive(NatZero))(ctx) match
                    case true =>
                      checkInferType(forNext) match
                        case InferResult.Ok(forNextTpe) =>
                          val expected = PiType(NatType, n => PiType(motive(n), _ => motive(Suc(n))))
                          eqNormalizingNoCheck(forNextTpe, expected)(ctx) match
                            case true => Ok(PiType(NatType, motive))
                            case false => Fail("ForN type mismatch with motive")
                        case f: InferResult.Fail => f
                    case false => Fail("Expected NatRec forZero to be of the motive type, but got: " + forZero + s" and motive is: ${motive(NatZero)}")
                case f: InferResult.Fail => f
            case InferResult.Ok(tpe) => Fail("Expected NatRec motive to be a type, but got: " + instantiatedMotive)
            case f: InferResult.Fail => f
        case NatRecApply(natRec, nat) =>
          checkInferType(natRec) match
            // Todo what if it's not a natrec but a lambda - best case is i handle reduction anyway
            case InferResult.Ok(tpe) =>
              NonCheckingReducer(ctx).whnfNoCheck(tpe).term match
                case PiType(NatType, abs) =>
                  checkInferType(nat) match
                    case InferResult.Ok(NatType) =>
                      Ok(abs(nat))
                    case InferResult.Ok(other) =>
                      Fail(s"Expected NatRec arg to be nat, but got $nat o type: " + other)
                    case f: Fail => f
                case other => Fail(s"Expected natrec, but got: $natRec of type " + other)
            case f: Fail => InferResult.wrapFailure(f, "NatRecApply: NatRec has wrong type")
        case Term.NatType => Ok(Universe)
        case PathType(tpe, start, end) =>
          val i = PhantomInterval.fresh()
          checkInferType(tpe(i)) match
            case InferResult.Ok(Universe) =>
              checkInferType(start) match
                case InferResult.Ok(startType) =>
                  checkInferType(end) match
                    case InferResult.Ok(endType) =>
                      val expectedStartType = tpe(Zero)
                      val expectedEndType = tpe(One)
                      if eqNormalizingNoCheck(startType, expectedStartType)(ctx) &&
                        eqNormalizingNoCheck(endType, expectedEndType)(ctx)
                      then Ok(Universe)
                      else Fail(s"Path were expected to start with $expectedStartType and end with $expectedEndType, but is starting with $startType and ending with $endType")
                    case f: InferResult.Fail => f
                case f: InferResult.Fail => f
            case InferResult.Ok(_) => Fail()
            case f: InferResult.Fail => f
        case PathAbstraction(abs, metadata) =>
          val i = PhantomInterval.fresh()
          checkInferType(abs(i)) match
            case InferResult.Ok(absTypeUnderI) =>
              val abstractedType = (j: Interval) => NonIntrospectingIntervalReplacer(i, j).apply(absTypeUnderI)
              Ok(PathType(abstractedType, abs(Zero), abs(One)))
            case f: InferResult.Fail => f
        case PathElimination(term, intervalArg) =>
          checkInferType(term) match
            case InferResult.Ok(PathType(tpe, start, end)) =>
              Ok(tpe(intervalArg)) // TODO will normalization later be able to recoder start and end?
            case Ok(other) => Fail(s"Tried to apply ${other.getClass.getSimpleName} to interval")
            case f: InferResult.Fail => f
        case Term.Universe => Ok(Universe) // russel
        case PhantomVarOfType(tpe, _) => Ok(tpe) // we assume that phantom vars were constructed using trusted types
        case System(value, motive, needsRestr) =>
          val faces = value.map(_._1)
          if !needsRestr || Face.sufficientlyRestricted(faces)
          then
            // check that the motive is well-formed
            checkInferType(motive) match
              case InferResult.Ok(_) =>
                value.map {
                  case (face, term) =>
                    val newCtx = ctx.restricted(face)
                    NonReducingCheckerInferrer(newCtx).checkInferType(term) match
                      case InferResult.Ok(restrictedTermType) =>
                        if eqNormalizingNoCheck(restrictedTermType, motive)(newCtx)
                        then Ok(restrictedTermType)
                        else Fail(s"non eq to motive ($motive) to term ($restrictedTermType) for face $face")
                      case f: InferResult.Fail => InferResult.wrapFailure(f, s"wrong tpe under face $face")
                }.find(_.isInstanceOf[Fail]) match
                  case Some(fail) => fail
                  case None =>
                    // no we check the if terms are eq under the faces
                    value.flatMap { case (f1, t1) =>
                      value.map { case (f2, t2) =>
                        val f = Face.FaceMin(f1, f2)
                        val newCtx = ctx.restricted(f)
                        eqNormalizingNoCheck(t1, t2)(newCtx) match
                          case true => Ok(motive)
                          case false => Fail(s"$t1 and $t2 non eq under faces $f1 and $f2")
                      }
                    }.find(_.isInstanceOf[Fail]) match
                      case Some(fail) => fail
                      case None => Ok(motive)
              case f: InferResult.Fail => InferResult.wrapFailure(f, "System motive is not well-formed")
          else Fail(s"Insufficiently restricted faces: $faces")
        case Composition(a0, typeAndSystem) =>
          //More generally, we write
          //Γ ` a : A[ϕ1 7→ u1 , . . . , ϕk 7→ uk ] for Γ ` a : A and Γ, ϕi ` a = ui : A for i = 1, . . . , k
          /*
          plan:
          1. check that a0: A(i0)
           */
          // prerequisite: check that face is not i-dependent (could be solved at class level)
          val iDependentFaces = Seq(
            PhantomInterval.fresh(), PhantomInterval.fresh()
          ).map(i => typeAndSystem(i)._2.value.map(_._1))
          if iDependentFaces.head == iDependentFaces(1)
          then
            // check that the system itself is OK
            val iPh = PhantomInterval.fresh()
            val (phYpe, phSys) = typeAndSystem(iPh)
            checkInferType(phSys.copy(requiresFullRestriction = false)) match
              case InferResult.Ok(phSysTpe) =>
                if eqNormalazing(phYpe, phSysTpe)
                then // system itself OK, check a0:A(I0)
                  val (zerodTpe, zerodSystem) = typeAndSystem(Zero)
                  checkInferType(a0) match
                    case InferResult.Ok(a0InferredTpe) =>
                      if eqNormalazing(zerodTpe, a0InferredTpe)
                      then // all good, a0:A(I0), now restricted check
                        // the restricted check is that a0 = u(i0) modulo phi_k for all k in the sys
                        val allMustBeGood = zerodSystem.value.map {
                          case (phi, u0) =>
                            val newCtx = ctx.restricted(phi)
                            val nr = NonReducingCheckerInferrer(newCtx, skipChecksOnlyInfer)
                            if nr.eqNormalazing(a0, u0)
                            then Ok(u0)
                            else Fail(s"One of the faces in comp not compatible: $u0 != $a0 under $phi")
                        }
                        allMustBeGood.find(_.isInstanceOf[Fail]) match
                          case Some(fail) => InferResult.wrapFailure(fail.asInstanceOf[Fail], "and possible oythers")
                          case None =>
                            // mind that except for the ingerred type, we also infere equalities unher phi to u(I1)
                            Ok(typeAndSystem(One)._1)
                      else Fail("a0: A(0) is not true")
                    case f: Fail => f
                else Fail("Comp: System type not as expected")
              case f: Fail => f
          else Fail("Face is i-dependent")

      def eqNormalazing(t1: Term, t2: Term): Boolean =
        eqNormalizingNoCheck(t1, t2)(ctx)
    }
  }

  def whfNoCheck(term: Term, ctx: Context): Term =
    V2.NonCheckingReducer(ctx).whnfNoCheck(term).term

  def whf(term: Term, ctx: Context): Term =
    inferType(term, ctx)
    whfNoCheck(term, ctx)

  def fullyNormalize(term: Term, ctx: Context): Term = {
    inferType(term, ctx)
    fullyNormalizeNoCheck(term, ctx)
  }

  def fullyNormalizeNoCheck(term: Term, ctx: Context): Term =
    V2.NonCheckingReducer(ctx).fullyNormalizedNoCheck(term)

  def inferType(term: Term, ctx: Context): Term = V2.checkInferType(term, ctx) match
    case InferResult.Ok(tpe) => tpe
    case InferResult.Fail(msg) => throw new TypeCheckFailedException(msg)
}