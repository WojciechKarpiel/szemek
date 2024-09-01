import sbt.Keys.libraryDependencies

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.5.0"

lazy val root = (project in file("."))
  .settings(
    name := "szemek",
    idePackagePrefix := Some("pl.wojciechkarpiel.szemek"),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test"
  )
