package pl.wojciechkarpiel.szemek
package parser

import Term.{Lambda, NatType}

import org.scalatest.funsuite.AnyFunSuiteLike

class ParserTest extends AnyFunSuiteLike {

  test("testParse") {
    val res = Parser.parse("λx: NatType => S(x)")
    assert(res == Lambda(NatType, x => Term.Suc(x)))
  }
}