package pl.wojciechkarpiel.szemek
package core

import Interval.{One, Opp, Zero}

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers


// generated by claude, need more corner cases
class FaceTest extends AnyFlatSpec with Matchers {

  import Face.*

  "Face.reduce" should "handle base cases" in {
    reduce(ZeroFace) shouldBe ZeroFace
    reduce(OneFace) shouldBe OneFace
    reduce(EqZero(Interval.PhantomInterval(2))) shouldBe EqZero(Interval.PhantomInterval(2))
    reduce(EqOne(Interval.PhantomInterval(3))) shouldBe EqOne(Interval.PhantomInterval(3))
  }

  it should "simplify FaceMin expressions" in {
    reduce(FaceMin(ZeroFace, OneFace)) shouldBe ZeroFace
    reduce(FaceMin(OneFace, EqZero(Interval.PhantomInterval(1)))) shouldBe EqZero(Interval.PhantomInterval(1))
    reduce(FaceMin(EqOne(Interval.PhantomInterval(1)), EqZero(Interval.PhantomInterval(1)))) shouldBe ZeroFace
    reduce(FaceMin(EqZero(Interval.PhantomInterval(1)), EqZero(Interval.PhantomInterval(1)))) shouldBe EqZero(Interval.PhantomInterval(1))
  }

  it should "simplify FaceMax expressions" in {
    reduce(FaceMax(ZeroFace, OneFace)) shouldBe OneFace
    reduce(FaceMax(ZeroFace, EqOne(Interval.PhantomInterval(1)))) shouldBe EqOne(Interval.PhantomInterval(1))
    reduce(FaceMax(EqOne(Interval.PhantomInterval(1)), EqZero(Interval.PhantomInterval(1)))) shouldBe OneFace
    reduce(FaceMax(EqOne(Interval.PhantomInterval(1)), EqOne(Interval.PhantomInterval(1)))) shouldBe EqOne(Interval.PhantomInterval(1))
  }

  it should "repeatedly apply reductions" in {
    val complexFace = FaceMin(
      FaceMax(EqOne(Interval.PhantomInterval(1)), EqZero(Interval.PhantomInterval(1))),
      FaceMin(OneFace, EqZero(Interval.PhantomInterval(2)))
    )
    reduce(complexFace) shouldBe EqZero(Interval.PhantomInterval(2))
  }

  it should "not reduce too much (it's not a boolean algebra)" in {
    val f: Face = Face.EqOne(Interval.PhantomInterval(997))
    val i: Interval = Interval.PhantomInterval(1)
    val r = FaceMax(
      FaceMin(f, EqZero(i)),
      FaceMin(f, EqOne(i)),
    )
    reduce(r) shouldBe r
  }

  it should "compute congurence of intervals - example from paper 1" in {
    val i = Interval.PhantomInterval(1)
    val j = Interval.PhantomInterval(2)
    val f = Face.FaceMin(Face.EqZero(i), Face.EqOne(j))
    val up = UnorderedPair.apply
    val congruence = IntervalCongruence.fromFace(f)
    congruence shouldBe IntervalCongruence(
      up(Zero, i), up(One, Opp(i)),
      up(Zero, Opp(j)), up(One, j),
      up(i, Opp(j)), up(j, Opp(i)),
    )

    assert(congurentUnderRestriction(i, Zero, f))
    assert(congurentUnderRestriction(j, One, f))
  }
  it should "compute congurence of intervals - example from paper 2" in {
    val i = Interval.PhantomInterval(1)
    val j = Interval.PhantomInterval(2)
    val f = Face.FaceMax(
      Face.FaceMin(Face.EqZero(i), Face.EqOne(j)),
      Face.FaceMin(Face.EqOne(i), Face.EqZero(j)),
    )
    IntervalCongruence.fromFace(f) shouldBe IntervalCongruence(Set(UnorderedPair(Opp(i), j), UnorderedPair(i, Opp(j))))
    Face.congurentUnderRestriction(i, Opp(j), f) shouldBe true
    assert(congurentUnderRestriction(i, i, f))
    assert(congurentUnderRestriction(Opp(j), i, f))
  }


  "suff restrctin  " should "suff restr" in {
    val i = PhantomInterval.fresh()
    val k = PhantomInterval.fresh()
    val s = Seq(EqOne(i), EqZero(i))
    assert(sufficientlyRestricted(s))
    assert(sufficientlyRestricted(s))
    assert(!sufficientlyRestricted(Seq(EqZero(i)) ++ Seq(EqOne(k))))
    assert(!sufficientlyRestricted(Seq(EqOne(k))))
    assert(sufficientlyRestricted(s ++ Seq(EqOne(k))))
    assert(sufficientlyRestricted(Seq(EqZero(k)) ++ s ++ Seq(EqOne(k))))

  }
  it should "rly resttict" in {

    assert(sufficientlyRestricted(Seq(EqZero(Zero), EqOne(Zero))))
    assert(sufficientlyRestricted(Seq(EqZero(One), EqOne(One))))

  }

  "congruence" should "fly" in {
    val i = PhantomInterval.fresh()
    val j = PhantomInterval.fresh()
    val fIn = Face.EqZero(j)

    val a = Interval.Min(i, j)

    assert(congurentUnderRestriction(a, Zero, fIn))
    assert(congurentUnderRestriction(Zero, a, fIn))
  }
}
