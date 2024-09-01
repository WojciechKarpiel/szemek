package pl.wojciechkarpiel.szemek

import TypeChecking.ensureTypeNoNormalisation

enum Term:
  // Pi type
  case Lambda(argType: Term, abs: Term => Term)
  case PiType(argType: Term, abs: Term => Term)
  case Application(fun: Term, arg: Term)
  // Sigma type
  case Pair(fst: Term, snd: Term)
  case SigmaType(argType: Term, abs: Term => Term)
  case Fst(pair: Term)
  case Snd(pair: Term)
  // Natural numbers
  case NatZero
  case Suc(n: Term)
  case NatRecursion() // TODO
  case NatType
  // Path
  case PathType(tpe: Term, start: Term, end: Term)
  case PathAbstraction(abs: Interval => Term)
  case PathElimination(term: Term, arg: Interval)


enum Interval:
  case Zero
  case One
  case Opp(i: Interval)
  case Min(i1: Interval, i2: Interval)
  case Max(i1: Interval, i2: Interval)

object Interval {
  def normalize(i: Interval): Interval = i match
    case Zero => Zero
    case One => One
    case opp@Interval.Opp(i) => normalize(i) match
      case Zero => One
      case One => Zero
      case _ => opp
    case min@Min(i1, i2) =>
      normalize(i1) match
        case Zero => Zero
        case _ => normalize(i2) match
          case Zero => Zero
          case _ => min
    case max@Max(i1, i2) =>
      normalize(i1) match
        case One => One
        case _ => normalize(i2) match
          case One => One
          case _ => max
}

extension (i: Interval)
  def normalize: Interval = Interval.normalize(i)

class TypeCheckFailedException() extends RuntimeException() /*with NoStackTrace*/

class Context
object Context{
  val Empty : Context = Context()
}


object TypeChecking {

  import Term.*

  def ensureTypeNoNormalisation(term: Term, tpe: Term, context: Context): Unit = { // TODO
    // hack for basic unit testing
    if tpe == NatType && (term != NatZero && term != Suc(NatZero)) then throw TypeCheckFailedException()


  }
  def whfNormalize(term: Term, context: Context): Term = term match
    case Term.Lambda(argType, abs) => ???
    case Term.PiType(argType, abs) => ???
    case Term.Application(fun, arg) => ???
    case Term.Pair(fst, snd) => ???
    case Term.SigmaType(argType, abs) => ???
    case Term.Fst(pair) => ???
    case Term.Snd(pair) => ???
    case Term.NatZero => NatZero
    case Term.Suc(n) => Suc(n)
    case Term.NatRecursion() => ???
    case Term.NatType => NatType
    case pTpe@PathType(tpe, start, end) => pTpe
    case Term.PathAbstraction(abs) => ???
    case PathElimination(eliminated, arg) =>
      whfNormalize(eliminated, context) match {
        case elNorm@PathType(tpe, start, end) =>
          ensureTypeNoNormalisation(start, tpe, context)
          ensureTypeNoNormalisation(end, tpe, context)
          arg.normalize match {
            case Interval.Zero => whfNormalize(start, context)
            case Interval.One => whfNormalize(end, context)
            case _ => PathElimination(elNorm, arg)
          }
        case elNorm => PathElimination(elNorm, arg)
      }

  def typecheck(term: Term, context: Context): Unit = term match {
    case Term.Lambda(argType, abs) => ???
    case Term.PiType(argType, abs) => ???
    case Term.Application(fun, arg) => ???
    case Term.Pair(fst, snd) => ???
    case Term.SigmaType(argType, abs) => ???
    case Term.Fst(pair) => ???
    case Term.Snd(pair) => ???
    case Term.NatZero => ()
    case Term.Suc(n) => ???
    case Term.NatRecursion() => ???
    case Term.NatType => ???
    case Term.PathType(tpe, start, end) =>
      //      ensureLegitType(tpe, context)
      //      ensureType(start, tpe, context)
      //      ensureType(end, tpe, context)
      ???
    case Term.PathAbstraction(abs) => ???
    case Term.PathElimination(term, arg) => ???
  }
}