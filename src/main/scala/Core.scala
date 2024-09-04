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
  // Univ
  case Universe

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

  private def checkPiInference(term: PiType, context:Context):Unit =
    ensureType(term.argType,context)
    ensureType(term.abs.apply(term.argType),context)

//  private def inferLambdaType(lambda: Term.Lambda, context: Context): PiType = lambda match {
//    case Lambda(argType, abs) =>
//      PiType(argType, arg => abs(arg))
//  }

   def ensureIsOfType(term_ : Term, tpe_ : Term, context: Context):Unit = {
    val term = applyRewriteRules(term_, context)
    val  tpe = applyRewriteRules(tpe_, context)
    term match
      case  Lambda(argTL,bdy) =>
        tpe match
          case PiType(argTP, tpeB) =>
            if argTL != argTP then throw new TypeCheckFailedException()
            ensureIsOfType(bdy(argTL), tpeB(argTP), context)
          case _ => throw new TypeCheckFailedException()
      case Suc(n) => // todo typecheck expensive?
        if tpe != NatType then throw new TypeCheckFailedException()
        ensureIsOfType(n, NatType, context)
      case NatZero =>
        if tpe != NatType then throw new TypeCheckFailedException()
      case NatType =>
        if tpe != Universe then throw new TypeCheckFailedException()
      case _ => ???
  }

  def applyRewriteRules(term: Term, context: Context): Term = term match
    case Term.NatRecursion() => ???
    case Term.Application(fun, arg) =>
      // 1. Check that fun is A -> B
      applyRewriteRules(fun,context) match
         case Term.Lambda(argType, abs) =>
           ensureType(argType, context) // this replaces check that l is of Pi type
           // 2. Check that arg is A
           ensureIsOfType(arg, argType, context)
           applyRewriteRules(abs.apply(arg), context)
         case fNorm => Application(fNorm, arg)

    case PathElimination(eliminated, arg) =>
      applyRewriteRules(eliminated, context) match {
        case elNorm@PathType(tpe, start, end) =>
          ensureTypeNoNormalisation(start, tpe, context)
          ensureTypeNoNormalisation(end, tpe, context)
          arg.normalize match {
            case Interval.Zero => applyRewriteRules(start, context)
            case Interval.One => applyRewriteRules(end, context)
            case _ => PathElimination(elNorm, arg)
          }
        case elNorm => PathElimination(elNorm, arg)
      }
    case f: Term.Fst => ???
    case s: Term.Snd => ???

      // Rest is already normal
    case l: Term.Lambda => l
    case pi: Term.PiType => pi
    case p: Term.Pair => p
    case s: Term.SigmaType => s
    case Term.NatZero => NatZero
    case s: Term.Suc => s
    case Term.NatType => NatType
    case pTpe: PathType => pTpe
    case pa: Term.PathAbstraction => pa


  private def ensureType(term: Term, context: Context):Unit =
   applyRewriteRules(term,context) match {
    case Term.PiType(_, _) => ()
    case Term.SigmaType(_, _) => ()
    case Term.NatType => ()
    case Term.PathType(_, _, _) => () /// TODO is path OK here?
    case _ => throw TypeCheckFailedException()
  }
  def validTerm(term: Term, context: Context): Unit = term match {
    case Term.Lambda(argType, abs) => // TODO normalize?
        ensureType(argType, context)

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