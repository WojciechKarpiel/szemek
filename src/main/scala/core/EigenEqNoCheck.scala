package pl.wojciechkarpiel.szemek
package core

import Term.*
import Term.EigenVal.Constraint.IdenticalTo
import Term.EigenVal.Constraints
import TypeChecking.V2.NonCheckingReducer
import core.EigenEqNoCheck.Result
import core.EigenEqNoCheck.Result.{IsEq, NonEq}

class EigenEqNoCheck(ctx: Context) {
  def equals(a: Term, b: Term): EigenEqNoCheck.Result = topLevel(a, b)

  private def topLevel(a: Term, b: Term): EigenEqNoCheck.Result = {
    if a == b then EigenEqNoCheck.Result.IsEq(Seq())
    else {
      val t1n = NonCheckingReducer(ctx, unfoldDefinitions = false).whnfNoCheck(a).term
      val t2n = NonCheckingReducer(ctx, unfoldDefinitions = false).whnfNoCheck(b).term
      eqWhf(t1n, t2n)
    }
  }

  // UWAGA: Co jeśli App(Globaldef, x) możnba uprościć, tylko to wymaga odwinięcia definicji?
  // trzeba się upwwniż że noncheckingreducer to obsługuje!!!
  private def eqWhf(a: Term, b: Term): EigenEqNoCheck.Result = {
    (a, b) match {
      case (e1: EigenVal, e2: EigenVal) => if e1 == e2 then EigenEqNoCheck.Result.IsEq(Seq())
      else EigenEqNoCheck.Result.IsEq(Seq(IdenticalTo(e1, e2)))
      case (e1: EigenVal, other) => EigenEqNoCheck.Result.IsEq(Seq(IdenticalTo(e1, other)))
      case (other, e2: EigenVal) => EigenEqNoCheck.Result.IsEq(Seq(IdenticalTo(other, e2)))
      // remember that defs are not unfolded, unfold if necessary
      case (GlobalVar(id1), GlobalVar(id2)) => // TODO SHOULD GLOBALS BE BEFORE EIGENS?
        if id1 == id2 then EigenEqNoCheck.Result.IsEq(Seq())
        else {
          val def1 = ctx.get(id1).get // todo how to handle None ?
          val def2 = ctx.get(id2).get
          topLevel(def1, def2)
        }
      case (GlobalVar(id), other) =>
        val defn = ctx.get(id).get // todo how to handle None ?
        topLevel(defn, other)
      case (other, GlobalVar(id)) =>
        val defn = ctx.get(id).get // todo how to handle None ?
        topLevel(other, defn)
      case (TypedTerm(term1, type1), TypedTerm(term2, tpe2)) =>
        topLevel(term1, term2) match
          case Result.NonEq => Result.NonEq
          case Result.IsEq(constr) => topLevel(type1, tpe2) match
            case Result.NonEq => Result.NonEq
            case Result.IsEq(constr2) => Result.IsEq(constr ++ constr2)
      case (TypedTerm(t, _), b) => topLevel(t, b)
      case (a, TypedTerm(t, _)) => topLevel(a, t)
      case (NatType, NatType) => EigenEqNoCheck.Result.IsEq(Seq())
      case (_, NatType) | (NatType, _) => EigenEqNoCheck.Result.NonEq
      case (Suc(n1), Suc(n2)) => topLevel(n1, n2)
      case (Suc(_), _) | (_, Suc(_)) => EigenEqNoCheck.Result.NonEq
      case (NatZero, NatZero) => EigenEqNoCheck.Result.IsEq(Seq())
      case (NatZero, _) | (_, NatZero) => EigenEqNoCheck.Result.NonEq
      case (l1@Lambda(t1, f1), l2@Lambda(t2, f2)) => eqAbstraction(l1.abstraction, l2.abstraction)
      case (Lambda(_, _), _) | (_, Lambda(_, _)) => EigenEqNoCheck.Result.NonEq
      case (p1: PiType, p2: PiType) => eqAbstraction(p1.abstraction, p2.abstraction)
      case (PiType(_, _), _) | (_, PiType(_, _)) => EigenEqNoCheck.Result.NonEq
      case (Application(fun1, arg1), Application(fun2, arg2)) =>
        topLevel(fun1, fun2) match
          case Result.NonEq => Result.NonEq
          case Result.IsEq(constr) => topLevel(arg1, arg2) match
            case Result.NonEq => Result.NonEq
            case Result.IsEq(constr2) => Result.IsEq(constr ++ constr2)
      case (Application(_, _), _) | (_, Application(_, _)) => EigenEqNoCheck.Result.NonEq
      case (PairIntro(fst1, snd1, motive1), PairIntro(fst2, snd2, motive2)) =>
        topLevel(fst1, fst2) match
          case Result.NonEq => Result.NonEq
          case Result.IsEq(constrFst) =>
            topLevel(snd1, snd2) match
              case Result.NonEq => Result.NonEq
              case Result.IsEq(constrSnd) =>
                val phi = PhantomVarOfType.fresh(fst1)
                val in1 = motive1(phi)
                val in2 = motive2(phi)
                topLevel(in1, in2) match
                  case Result.NonEq => Result.NonEq
                  case Result.IsEq(constrMot /* can contain phi */) =>
                    Result.IsEq(constrFst ++ constrSnd ++ constrMot)
      case (PairIntro(_, _, _), _) | (_, PairIntro(_, _, _)) => Result.NonEq
      case (p1@PairType(_, _), p2@PairType(_, _)) => eqAbstraction(p1.abstraction, p2.abstraction)
      case (PairType(_, _), _) | (_, PairType(_, _)) => Result.NonEq
      case (Fst(p1), Fst(p2)) => topLevel(p1, p2)
      case (Fst(_), _) | (_, Fst(_)) => Result.NonEq
      case (Snd(p1), Snd(p2)) => topLevel(p1, p2)
      case (Snd(_), _) | (_, Snd(_)) => Result.NonEq
      case (Universe, Universe) => Result.IsEq(Seq())
      case (Universe, _) | (_, Universe) => Result.NonEq
      case (p1: PhantomVarOfType, p2: PhantomVarOfType) => if p1 == p2 then Result.IsEq(Seq()) else NonEq
      case (_: PhantomVarOfType, _) | (_, _: PhantomVarOfType) => NonEq
      case (NatRecursion(motive1, forZero1, forNext1), NatRecursion(motive2, forZero2, forNext2)) =>
        val phi = PhantomVarOfType.fresh(NatType)
        val inst1 = motive1(phi)
        val inst2 = motive2(phi)
        topLevel(inst1, inst2) match
          case Result.NonEq => NonEq
          case Result.IsEq(motiveConstr) =>
            topLevel(forZero1, forZero2) match
              case Result.NonEq => NonEq
              case Result.IsEq(forZeroConstr) =>
                topLevel(forNext1, forNext2) match
                  case Result.NonEq => NonEq
                  case Result.IsEq(forNextConstr) => Result.IsEq(motiveConstr ++ forZeroConstr ++ forNextConstr)
      case (_: NatRecursion, _) | (_, _: NatRecursion) => NonEq
      case (NatRecApply(natRec1, nat1), NatRecApply(natRec2, nat2)) =>
        topLevel(natRec1, natRec2) match
          case Result.NonEq => NonEq
          case Result.IsEq(nrConstr) =>
            topLevel(nat1, nat2) match
              case NonEq => NonEq
              case IsEq(cn) => Result.IsEq(nrConstr ++ cn)
      case (_: NatRecApply, _) | (_, _: NatRecApply) => NonEq
      case (s1: System, s2: System) => if s1 == s2 then IsEq(Seq()) else NonEq // TODO
      case (_: System, _) | (_, _: System) => NonEq
      case (s1: Composition, s2: Composition) => if s1 == s2 then IsEq(Seq()) else NonEq // TODO
      case (_: Composition, _) | (_, _: Composition) => NonEq

      case  (PathAbstraction(abs1, _:Metadata), PathAbstraction(abs2, _:Metadata)) =>
        val i = PhantomInterval.fresh()
        topLevel(abs1(i), abs2(i))
      case  (_: PathAbstraction, _)|(_,_: PathAbstraction) => NonEq
      // TODO congruences for paths
      case (PathElimination(term1, arg1), PathElimination(term2, arg2)) =>
        topLevel(term1, term2) match
          case Result.NonEq => Result.NonEq
          case Result.IsEq(constrTerm) => // TODO special case when arg is not even used
            if ctx.congruent(arg1, arg2) then Result.IsEq(constrTerm) else Result.NonEq
      case (PathElimination(_, _), _) | (_, PathElimination(_, _)) => Result.NonEq
      case (PathType(tpe1, start1, end1), PathType(tpe2, start2, end2)) =>
        val i = PhantomInterval.fresh()
        topLevel(tpe1(i), tpe2(i)) match
          case Result.NonEq => Result.NonEq
          case Result.IsEq(constrTpe) =>
            topLevel(start1, start2) match
              case Result.NonEq => Result.NonEq
              case Result.IsEq(constrStart) =>
                topLevel(end1, end2) match
                  case Result.NonEq => Result.NonEq
                  case Result.IsEq(constrEnd) => Result.IsEq(constrTpe ++ constrStart ++ constrEnd)
    }
  }

  private def eqAbstraction(a: Abstraction, b: Abstraction): EigenEqNoCheck.Result = {
    val t1 = a.argType
    val t2 = b.argType
    val f1 = a.abs
    val f2 = b.abs
    topLevel(t1, t2) match {
      case EigenEqNoCheck.Result.NonEq => EigenEqNoCheck.Result.NonEq
      case EigenEqNoCheck.Result.IsEq(constrFromTpe) =>
        val phi = PhantomVarOfType.fresh(t1)
        val inst1 = f1(phi)
        val inst2 = f2(phi)
        topLevel(inst1, inst2) match {
          case EigenEqNoCheck.Result.NonEq => EigenEqNoCheck.Result.NonEq
          case EigenEqNoCheck.Result.IsEq(constrFromInst) => EigenEqNoCheck.Result.IsEq(constrFromTpe ++ constrFromInst)
        }
    }
  }
}

object EigenEqNoCheck {
  enum Result:
    case NonEq // TODO add noneq reason and trace
    case IsEq(constr: Constraints)
}