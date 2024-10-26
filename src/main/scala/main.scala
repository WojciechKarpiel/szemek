package pl.wojciechkarpiel.szemek

import TypeChecking.V2.InferResult
import TypeChecking.{V2, fullyNormalizeNoCheck}
import parser.Parser

@main
def main(): Unit = {
  import scala.io.StdIn.readLine
  val input = readLine("Enter the term to parse: ")
  val parsedTerm = Parser.parse(input)
  val ctx = Context.Empty
  V2.checkInferType(parsedTerm, ctx) match
    case InferResult.Ok(tpe) => println("Type: " + tpe)
      val r = fullyNormalizeNoCheck(parsedTerm, ctx)
      println("Normalized: " + r)
    case fail: InferResult.Fail =>
      println("Type error: " + fail)
      System.exit(1)
}

