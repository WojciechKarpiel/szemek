package pl.wojciechkarpiel.szemek
package core

import Interval.{Max, Min, One, Opp, PhantomInterval, Zero}

import scala.annotation.tailrec
import scala.collection.mutable

enum Face:
  case ZeroFace
  case OneFace
  case EqZero(i: Interval)
  case EqOne(i: Interval)
  case FaceMin(f1: Face, f2: Face)
  case FaceMax(f1: Face, f2: Face)

object Face:
  // TODO imlement it

  /** Γ |- ϕ1 ∨ · · · ∨ ϕn = 1F : F. */
  def sufficientlyRestricted(f: Seq[Face]): Boolean = /* f.isEmpty|| */ {

    val f2 = f.map(reduce)
    val zerod = mutable.Set[Interval]()
    val oned = mutable.Set[Interval]()

    f2.foreach {
      case one: Face.EqOne => oned.add(one.i)
      case zero: Face.EqZero => zerod.add(zero.i)
      case _ =>
    }

    val f3 = f2.map {
      case EqOne(i) if zerod.contains(i) && oned.contains(i) => OneFace
      case EqZero(i) if oned.contains(i) && zerod.contains(i) => OneFace
      case f => f
    }

    sufficientlyRestricted(f3.reduce(FaceMax.apply))
  }

  def sufficientlyRestricted(f: Face): Boolean = Face.reduce(f) == OneFace


  private def reduceStep(f: Face): Face = f match
    case Face.ZeroFace => ZeroFace
    case Face.OneFace => OneFace
    case Face.EqZero(Zero) => OneFace
    case Face.EqOne(One) => OneFace
    case Face.EqZero(One) => ZeroFace
    case Face.EqOne(Zero) => ZeroFace
    case Face.EqZero(i) => EqZero(i.normalize)
    case Face.EqOne(i) => EqOne(i.normalize)
    case Face.FaceMin(f1, f2) =>
      (reduceStep(f1), reduceStep(f2)) match
        case (ZeroFace, _) => ZeroFace
        case (_, ZeroFace) => ZeroFace
        case (OneFace, x) => x
        case (x, OneFace) => x
        case (EqZero(i), EqOne(j)) if i.normalize == j.normalize => ZeroFace
        case (EqOne(i), EqZero(j)) if i.normalize == j.normalize => ZeroFace
        case (x, y) if x == y => x
        case (x, y) => Face.FaceMin(x, y)
    case Face.FaceMax(f1, f2) =>
      (reduceStep(f1), reduceStep(f2)) match
        case (OneFace, _) => OneFace
        case (_, OneFace) => OneFace
        case (ZeroFace, x) => x
        case (x, ZeroFace) => x
        case (EqZero(i), EqOne(j)) if i.normalize == j.normalize => OneFace
        case (EqOne(i), EqZero(j)) if i.normalize == j.normalize => OneFace
        case (x, y) if x == y => x
        case (x, y) => Face.FaceMax(x, y)

  @tailrec
  def reduce(f: Face): Face =
    val r = reduceStep(f)
    if r == f then r else reduce(r)


  case class UnorderedPair(a: Interval, b: Interval) {
    def toSet: Set[Interval] = Set(a, b)

    override def equals(obj: Any): Boolean = obj != null && obj.isInstanceOf[UnorderedPair] &&
      obj.asInstanceOf[UnorderedPair].toSet == toSet

    override def hashCode(): Int = toSet.hashCode()

    def contains(i: Interval): Boolean = toSet.contains(i)
  }

  case class IntervalCongruence(value: Set[UnorderedPair]) {

    def exFalsoQuodlibet: Boolean = value.contains(UnorderedPair(Interval.Zero, Interval.One))
  }

  object IntervalCongruence {

    def apply(unorderedPairs: UnorderedPair*): IntervalCongruence =
      apply(unorderedPairs.toSet)

    @tailrec
    private def transitiveClosure(value: Set[UnorderedPair]): Set[UnorderedPair] = {
      val newPairs: Set[Seq[UnorderedPair]] = for {
        p1 <- value
        p2 <- value
        if p1.contains(p2.a) || p1.contains(p2.b)
        // can be lazy
        possibleNew = Seq(UnorderedPair(p1.a, p2.a),
          UnorderedPair(p1.a, p2.b),
          UnorderedPair(p1.b, p2.a),
          UnorderedPair(p1.b, p2.b),
        ).filterNot(d => d.a == d.b)
        if possibleNew.exists(!value.contains(_))
      } yield possibleNew
      if newPairs.isEmpty then value else transitiveClosure(value ++ newPairs.flatten)
    }

    // todo reduce first
    def fromFace(f: Face): IntervalCongruence = {
      f match
        case Face.ZeroFace => ??? // degenerated everything congruent to everything
        case Face.OneFace => IntervalCongruence.apply() // no special congruence, just identity
        case Face.EqZero(i) => IntervalCongruence(UnorderedPair(i, Interval.Zero), UnorderedPair(Opp(i).normalize, Interval.One))
        case Face.EqOne(i) => IntervalCongruence(UnorderedPair(i, Interval.One), UnorderedPair(Opp(i).normalize, Interval.Zero))
        case Face.FaceMin(f1, f2) => IntervalCongruence(transitiveClosure(fromFace(f1).value.union(fromFace(f2).value)))
        case Face.FaceMax(f1, f2) => IntervalCongruence(fromFace(f1).value.intersect(fromFace(f2).value))

    }
  }


  
  def congurentUnderRestriction(i0: Interval, i1: Interval, f: Face): Boolean = {
    val congruence = IntervalCongruence.fromFace(f)
    congurentUnderRestriction(i0, i1, congruence)
  }


  def simplifyObviousCongruences(i: Interval, congruence: IntervalCongruence): Interval = {
    def wrk(j: Interval) = {
      var iNorm = j
      val c0 = congruence.value.contains(UnorderedPair(Zero, iNorm))
      val c1 = congruence.value.contains(UnorderedPair(One, iNorm))
      if c1 && c0 then throw new TypeCheckFailedException()
      if c0 then iNorm = Zero
      if c1 then iNorm = One
      iNorm
    }


    val j = i match
      case Interval.Zero => Zero
      case Interval.One => One
      case Interval.Opp(i) => Opp(simplifyObviousCongruences(wrk(i), congruence))
      case Interval.Min(i1, i2) => Min(simplifyObviousCongruences(wrk(i1), congruence), simplifyObviousCongruences(wrk(i2), congruence))
      case Interval.Max(i1, i2) => Max(simplifyObviousCongruences(wrk(i1), congruence), simplifyObviousCongruences(wrk(i2), congruence))
      case Interval.PhantomInterval(id) => PhantomInterval(id)

    j
  }

  def congurentUnderRestriction(i0: Interval, i1: Interval, congruence: IntervalCongruence): Boolean = {

    def work(i0: Interval, i1: Interval): Boolean = {
      val ret = i0 == i1 || congruence.value.exists(p => p.contains(i0) && p.contains(i1)) // can be done lazily in `false` bramches
      if ret then ret else {
        i0 match
          case Interval.Zero => false
          case Interval.One => false
          case Interval.Opp(i) =>
            // or check for sending 1 to 0? dunno how to handle it here
            i1.isInstanceOf[Interval.Opp] && work(i, i1.asInstanceOf[Interval.Opp].i)
          case Interval.Min(i11, i12) => i1.isInstanceOf[Interval.Min] && {
            val i1_ = i1.asInstanceOf[Interval.Min]
            (work(i11, i1_.i1) && work(i12, i1_.i2)) || (work(i12, i1_.i1) && work(i11, i1_.i2))
          }
          case Interval.Max(i11, i12) => i1.isInstanceOf[Interval.Max] && {
            val i1_ = i1.asInstanceOf[Interval.Max]
            (work(i11, i1_.i1) && work(i12, i1_.i2)) || (work(i12, i1_.i1) && work(i11, i1_.i2))
          }
          case Interval.PhantomInterval(id) => false
      }
    }

    //    if congruence == DegenerateCongruence then true else
    work(simplifyObviousCongruences(i0, congruence).normalize, simplifyObviousCongruences(i1, congruence).normalize)
  }

  def subInterval(input_ : Interval, swapInput_ : Interval, swapOutput_ : Interval): Interval = {
    val swapInput = swapInput_.normalize
    val swapOutput = swapOutput_.normalize

    val input = input_.normalize

    def work(in: Interval, swin: Interval, swout: Interval): Interval = in match
      case Interval.Zero => if in == swin then swout else in // todo doesn't make sense to swap 0 and 1
      case Interval.One => if in == swin then swout else in
      case Interval.Opp(i) => Opp(work(i, swin, swout))
      case Interval.Min(i1, i2) => Min(work(i1, swin, swout), work(i2, swin, swout))
      case Interval.Max(i1, i2) => Max(work(i1, swin, swout), work(i2, swin, swout))
      case Interval.PhantomInterval(_) => if in == swin then swout else in

    work(input, swapInput, swapOutput)
  }