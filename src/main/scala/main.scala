package pl.wojciechkarpiel.szemek

import parser.Parser

@main
def main(): Unit = {
  import scala.io.StdIn.readLine

  val input = readLine("Enter the term to parse: ")
  try {
    val parsedTerm = Parser.parse(input)
    val typeq = TypeChecking.inferType(parsedTerm, Context.Empty)
    println(s"Type: $typeq")
    val normalizedTerm = TypeChecking.fullyNormalize(parsedTerm, Context.Empty)
    println(s"Normalized Term: $normalizedTerm")
  } catch {
    case e: Exception =>
      println(s"Error: ${e.getMessage}")
      throw e
  }
}

