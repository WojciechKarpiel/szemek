package pl.wojciechkarpiel.szemek

import Interval.*

import org.scalatest.*
import org.scalatest.flatspec.*
import org.scalatest.matchers.*

class IntervalTest extends AnyFlatSpec with should.Matchers {

  "Interval" should "normalize" in {
    Zero.normalize should be(Zero)
    One.normalize should be(One)
    Opp(Zero).normalize should be(One)
    Opp(One).normalize should be(Zero)
    Min(Zero, One).normalize should be(Zero)
    Min(One, Zero).normalize should be(Zero)
    Max(Zero, One).normalize should be(One)
    Max(One, Zero).normalize should be(One)

    Interval.normalize(Interval.Min(One, PhantomInterval(31))) should be(PhantomInterval(31))
    Interval.normalize(Interval.Min(PhantomInterval(3), One)) should be(PhantomInterval(3))
    Interval.normalize(Interval.Max(PhantomInterval(3), Zero)) should be(PhantomInterval(3))
  }
}
