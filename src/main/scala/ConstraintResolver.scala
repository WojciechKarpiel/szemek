package pl.wojciechkarpiel.szemek

import Term.EigenVal
import Term.EigenVal.Constraint

import pl.wojciechkarpiel.szemek.Term.EigenVal.Constraint.{IdenticalTo, IsOfType}
import pl.wojciechkarpiel.szemek.TypeChecking.V2.InferResult.Ok

object ConstraintResolver:
  type Substitutions = List[Substitution]

  private def applySubstitution(s: Substitution, term: Term): Term = term match
    case v: EigenVal => if v == s.from then s.to else term
    case _ => term // TODO deep inspect

  private def applySubstitutions(s: Substitutions, term: Term): Term = s.foldRight(term)(applySubstitution)

  private def occurs(e: EigenVal, t: Term): Boolean = false // TODO

  private def resolveOne(a: Constraint): Substitutions = {

    a match {
      case Constraint.IdenticalTo(a: EigenVal, b: EigenVal) =>
        if a == b then Nil
        else List(Substitution(a, b))
      case Constraint.IdenticalTo(a: EigenVal, b) => List(Substitution(a, b))
      case Constraint.IdenticalTo(a, b: EigenVal) => List(Substitution(b, a))
      case Constraint.IdenticalTo(a, b) => // todo deep inspect
        if a != b then throw new TypeCheckFailedException("TODO lack of deep eq inspect")
        else List()
      case Constraint.IsOfType(term, tpe) =>
        if !term.isEigenVal && !tpe.isEigenVal then {
          if TypeChecking.V2.checkInferType(term) == Ok(tpe) then Nil
          else throw new TypeCheckFailedException(s"Type check failed $term $tpe")
        }
        else throw new NotImplementedError(s"HEHEHEH $term $tpe")
    }
  }

  private def resolve(constaints: List[Constraint]): Substitutions = constaints match
    case ::(constr, rest) =>
      val t2 = resolve(rest)
      val newC: Constraint = constr match
        case Constraint.IdenticalTo(a, b) => IdenticalTo(applySubstitutions(t2, a), applySubstitutions(t2, b))
        case Constraint.IsOfType(term, tpe) => IsOfType(applySubstitutions(t2, term), applySubstitutions(t2, tpe))
      val t1 = resolveOne(newC)
      t1 ++ t2
    case Nil => Nil

  def resolveStarter(constraints: Seq[Constraint]): Substitutions = {
    constraints.partition(_.isInstanceOf[IdenticalTo]) match
      case (identicalTo, rest) =>
        resolve((identicalTo ++ rest).toList.reverse) // start with identical, easier cases
  }

  case class Substitution(from: EigenVal, to: Term)

