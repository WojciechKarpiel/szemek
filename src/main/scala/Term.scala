package pl.wojciechkarpiel.szemek

enum Term:
  case PathType(tpe: Term, start: Term, end: Term)
  case PathAbstraction(abs: Interval => Term)
  case PathElimination(term: Term, arg: Interval)

  case Zero

sealed trait Interval