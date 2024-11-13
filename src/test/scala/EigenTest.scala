package pl.wojciechkarpiel.szemek

import org.scalatest.funsuite.AnyFunSuiteLike
import pl.wojciechkarpiel.szemek.Term.{EigenVal, NatType, NatZero}
import pl.wojciechkarpiel.szemek.TypeChecking.V2
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult


class EigenTest extends AnyFunSuiteLike {

  test("eigen11") {
    val t = TypedTerm(NatZero, EigenVal.fresh())

    V2.checkInferTypeEig(t) match
      case InferResult.Ok(tpe) => assert(tpe == NatType)
      case f: InferResult.Fail => fail(f.toString)
  }

}
