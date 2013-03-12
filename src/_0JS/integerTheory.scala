package _0JS
import CL._
import SemanticHelpers._

object IntTheory {
  def solveMul(lhs: AV, rhs:AV, envAssumptions:Set[CLExp]): AV = {
    val lhsVar = CLVar(lhs.v)
    val rhsVar = CLVar(rhs.v)
    
    //lhs = 0 || rhs = 0 => ret = 0   
    if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar EQ CLNum(0))) || 
        (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar EQ CLNum(0)))) {
      val retVarName = ("num", BigInt(0), 0)
      AV(retVarName, Set(CLVar(retVarName) EQ CLNum(0)))
    }
    else if (lhs == rhs) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) > CLNum(0), CLVar(retVarName) >= lhsVar))
    }
    //lhs > 0 && rhs > 0 => ret > 0
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar > CLNum(0))) && 
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar > CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) > CLNum(0), CLVar(retVarName) >= lhsVar, CLVar(retVarName) >= rhsVar))
    }
    //lhs < 0 && rhs < 0 => ret > 0
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar < CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar < CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) > CLNum(0), CLVar(retVarName) > lhsVar, CLVar(retVarName) > rhsVar))
    }
    //lhs > 0 && rhs < 0 => ret < 0
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar > CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar < CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) < CLNum(0), CLVar(retVarName) < lhsVar, CLVar(retVarName) LEQ rhsVar))
    }
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar < CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar > CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) < CLNum(0), CLVar(retVarName) LEQ lhsVar, CLVar(retVarName) < rhsVar))
    }
    // > >=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar > CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar >= CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) >= CLNum(0), CLVar(retVarName) >= rhsVar))
    }
    // > <=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar > CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar LEQ CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) LEQ CLNum(0), CLVar(retVarName) LEQ rhsVar, CLVar(retVarName) < lhsVar))
    }
    // < >=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar < CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar >= CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) LEQ CLNum(0), CLVar(retVarName) LEQ rhsVar))
    }
    // < <=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar < CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar LEQ CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) >= CLNum(0), CLVar(retVarName) >= rhsVar, CLVar(retVarName) > lhsVar))
    }
    // >= >
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar >= CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar > CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) >= CLNum(0), CLVar(retVarName) >= lhsVar))
    }
    // >= <
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar >= CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar < CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) LEQ CLNum(0), CLVar(retVarName) LEQ lhsVar))
    }
    // <= >
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar LEQ CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar > CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) LEQ CLNum(0), CLVar(retVarName) LEQ lhsVar, CLVar(retVarName) < rhsVar))
    }
    // <= <
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar LEQ CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar < CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) >= CLNum(0), CLVar(retVarName) > rhsVar, CLVar(retVarName) >= lhsVar))
    }
    // >= >=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar >= CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar >= CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) >= CLNum(0), CLVar(retVarName) >= lhsVar, CLVar(retVarName) >= rhsVar))
    }
    // >= <=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar >= CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar LEQ CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) LEQ CLNum(0), CLVar(retVarName) LEQ lhsVar))
    }
    // <= >=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar LEQ CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar >= CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) LEQ CLNum(0), CLVar(retVarName) LEQ rhsVar))
    }
    // <= <=
    else if ((Z3Solver.Z3Oracle(getConjunction(lhs.c ++ envAssumptions), lhsVar LEQ CLNum(0))) &&
             (Z3Solver.Z3Oracle(getConjunction(rhs.c ++ envAssumptions), rhsVar LEQ CLNum(0)))) {
      val retVarName = freshVariableName
      AV(retVarName, Set(CLVar(retVarName) >= CLNum(0), CLVar(retVarName) >= rhsVar, CLVar(retVarName) >= lhsVar))
    }
    else {
      AV(freshVariableName, Set(CLTrue))
    }
  }
}