package pl.wojciechkarpiel.szemek

import parser.{Location, NaiveLocation}

final case class Metadata(location: Location) {

  // hack to avoid breaking eq
  override def equals(obj: Any): Boolean = true

  override def hashCode(): Int = 0
}

object Metadata {
  val Empty: Metadata = Metadata(NaiveLocation(-1, -1))
}