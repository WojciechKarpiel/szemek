package pl.wojciechkarpiel.szemek

import Interval.*
import Term.*

import org.scalatest.funsuite.AnyFunSuiteLike
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult.Ok
import pl.wojciechkarpiel.szemek.TypeChecking.{checkCtx, fullyNormalize}

class E2Etest extends AnyFunSuiteLike {

  // TODO
  test("transport") {
    val in =
      """
        |def transport : Path () :=
        |""".stripMargin

  }

}
