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
  }
}
