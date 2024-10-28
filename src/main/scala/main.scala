package pl.wojciechkarpiel.szemek

import TypeChecking.V2.InferResult
import TypeChecking.{V2, fullyNormalizeNoCheck}
import parser.Parser

@main
def main(): Unit = {
  import scala.io.StdIn.readLine
  val input = readLine("Enter the term to parse: ")
  val parseResult = Parser.parse(input)
  var reconstructedCtx = Context.Empty
  parseResult.ctx.foreach {
    case (id, typedTerm) =>
      reconstructedCtx = reconstructedCtx.addChecking(id, typedTerm)
  }
  V2.checkInferType(parseResult.term, reconstructedCtx) match
    case InferResult.Ok(tpe) => println("Type: " + tpe)
      val r = fullyNormalizeNoCheck(parseResult.term, reconstructedCtx)
      println("Normalized: " + r)
    case fail: InferResult.Fail =>
      println("Type error: " + fail)
      System.exit(1)
}

