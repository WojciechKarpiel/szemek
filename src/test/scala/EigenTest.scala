package pl.wojciechkarpiel.szemek

import org.scalatest.funsuite.AnyFunSuiteLike
import pl.wojciechkarpiel.szemek.Term.{EigenVal, NatType, NatZero}
import pl.wojciechkarpiel.szemek.TypeChecking.V2
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult
import pl.wojciechkarpiel.szemek.parser.Parser


class EigenTest extends AnyFunSuiteLike {

  test("eigen11") {
    val t = Parser.parse("0 : _").term
    V2.checkInferTypeEig(t) match
      case InferResult.Ok(tpe) => assert(tpe == NatType)
      case f: InferResult.Fail => fail(f.toString)
  }

}
