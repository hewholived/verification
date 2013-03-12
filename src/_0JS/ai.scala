package _0JS

import scala.annotation.tailrec
import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{ListBuffer => MList}
import scala.collection.mutable.{Set => MSet}

import HelperTypeAliases._
import HelperObjects._

object NotJS {
  import java.io._
  import scala.io._

  def main(args: Array[String]) {
    val ast = ParseL.getAST( Source.fromFile( args(0) ).mkString )

    //Evaluator.eval(SemanticHelpers.inject(ast))
    println("Final Store: " + Evaluator.eval(SemanticHelpers.inject(ast))._2)
  }
}

