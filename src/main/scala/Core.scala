package pl.wojciechkarpiel.szemek


final case class Id(value: String) extends AnyVal

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
  // Varia
  case GlobalVar(id: Id)
  case PhantomVarOfType(tpe: Term)

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

class Context private(map: Map[Id, TypedTerm]) {
  def add(id: Id, term: TypedTerm): Context = new Context(map + (id -> term))

  def get(id: Id): Option[TypedTerm] = map.get(id)

  def isEmpty: Boolean = map.isEmpty

  def contains(id: Id): Boolean = map.contains(id)
}

object Context {
  val Empty: Context = new Context(Map())
}

final case class ContextTerm(term: Term, ctx: Context)

final case class Inference(preconditions: Seq[ContextTerm], result: ContextTerm)

final case class EqJudgement(rewriteFrom: Term, rewriteTo: Term, tpe: Term)

final case class TypedTerm(term: Term, tpe: Term)

object TypeChecking {

  import Term.*

  //Well-formed contexts
  def validContext(ctx: Context): Boolean = true

  // Well-formed types

  //  def natTypeInference(ctx: Context):Inference = Inference(Seq(), ContextTerm(NatType, ctx))


  def rewriteRule(term: Term, ctx: Context): Term = {
    term match
      case app@Term.Application(fun, arg) =>
        rewriteRule(fun, ctx) match
          case Term.Lambda(argType, abs) =>
            // this is supposed to check many things about the lbda
            // TODO: add test which make this check necessary
            if !inferType(fun, ctx).isInstanceOf[PiType] then throw new TypeCheckFailedException()
            if inferType(arg, ctx) == argType then abs(arg) else throw new TypeCheckFailedException()
          case _ => app
      case Term.PathElimination(term, arg) => ???
      case proj@Term.Fst(pair) =>
        rewriteRule(pair, ctx) match
          case Term.Pair(fst, _) =>
            if inferType(pair, ctx).isInstanceOf[Pair] then fst else throw new TypeCheckFailedException()
          case _ => proj
      case proj@Term.Snd(pair) =>
        rewriteRule(pair, ctx) match
          case Term.Pair(_, snd) =>
            if inferType(pair, ctx).isInstanceOf[Pair] then snd else throw new TypeCheckFailedException()
          case _ => proj
      case Term.NatRecursion() => ???
      case notRewritable => notRewritable
  }


  def inferType(term: Term, ctx: Context): Term = rewriteRule(term, ctx) match {
    case PhantomVarOfType(tpe) => // todo need to check if tpe is tpe?
      if inferType(tpe, ctx) == Universe then tpe else throw new TypeCheckFailedException()
    case Term.Universe => Universe
    case Term.GlobalVar(id) => ctx.get(id).map(_.tpe).getOrElse(throw new TypeCheckFailedException())
    case Term.NatType => Universe
    case Term.NatZero => NatType
    case Term.Suc(n) =>
      if inferType(n, ctx) == NatType then NatType
      else throw new TypeCheckFailedException()
    case Term.Lambda(argType, abs) =>
      // 1. Check that the Arg type is legit
      if inferType(argType, ctx) != Universe then throw new TypeCheckFailedException();
      // 2. Check if body type exsits
      val bodyType = inferType(abs(PhantomVarOfType(argType)), ctx)
      if inferType(bodyType, ctx) != Universe then throw new TypeCheckFailedException();
      PiType(argType, x => inferType(abs(x), ctx))

    case Term.Pair(fst, snd) => // TODO similar to Lambda
      ???
    case Term.PiType(argType, abs) => ???
    case Term.SigmaType(argType, abs) => ???
    case Term.PathType(tpe, start, end) => ???
    case Term.PathAbstraction(abs) => ???
    // has rewrite rules, but is not rewritable
    case Term.Application(fun, arg) => ???
    case Term.NatRecursion() => ???
    case Term.PathElimination(term, arg) => ???
    case Term.Fst(pair) => ???
    case Term.Snd(pair) => ???
  }
}