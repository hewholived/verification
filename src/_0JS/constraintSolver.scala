package _0JS

import CL._
import z3.scala._

object illegal extends Exception

object Z3Solver {
  def getVarSet(exp:CLExp): Set[String] = {
    exp match {
      case CLVar(v)           => Set(v._1 + "_" + v._2 + "_" + v._3)
      case CLBinop(e1, e2, _) => getVarSet(e1) ++ getVarSet(e2)
      case CLUnop(e, _)       => getVarSet(e)
      case _                  => Set()
    }
  }
  def evalAST(e:CLExp, z3:Z3Context, varASTMap:Map[String, Z3AST]): Z3AST = {
    val intSort:Z3Sort = z3.mkIntSort
      
    def eval(e:CLExp) : Z3AST = {
      e match {
        case CLVar(v) => varASTMap(v._1 + "_" + v._2 + "_" + v._3)
        case CLNum(n) => z3.mkInt(n.toInt, intSort)
        case CLTrue   => z3.mkTrue()
        case CLFalse  => z3.mkFalse()
        case CLBinop(e1, e2, op)     => {
          val (v1, v2) = (eval(e1), eval(e2))
          op match {
            case CLPlus => z3.mkAdd(v1, v2)
            case CLMinus => z3.mkSub(v1, v2)
            case CLTimes => z3.mkMul(v1, v2)
            case CLEquals => z3.mkEq(v1, v2)
            case CLNotEquals => z3.mkNot(z3.mkEq(v1, v2))
            case CLLessEquals => z3.mkLE(v1, v2)
            case CLGreaterEquals => z3.mkGE(v1, v2)
            case CLLess => z3.mkLT(v1, v2)
            case CLGreater => z3.mkGT(v1, v2)
            case CLImplies => z3.mkImplies(v1, v2)
            case CLAnd => z3.mkAnd(v1, v2)
            case CLOr => z3.mkOr(v1, v2)
            case _ => throw illegal
          }
        }
        case CLUnop(e1, op) => op match {
          case CLLogNot => z3.mkNot(eval(e1))
          case _ => throw illegal
        }
        case _ => throw illegal
      }
    }
    eval(e)
  }
  
  def Z3Oracle(lhs:CLExp, rhs:CLExp): Boolean = {
    val cfg = new Z3Config
    val z3 = new Z3Context(cfg)
    val intSort:Z3Sort = z3.mkIntSort
    
    val varSet = getVarSet(lhs) ++ getVarSet(rhs)
    val varASTMap = varSet.foldLeft(Map[String, Z3AST]())((map, v) => {
      map + (v -> z3.mkConst(z3.mkStringSymbol(v), intSort))
    })
   
    //!(a -> b) 
    z3.assertCnstr(z3.mkNot(z3.mkImplies(evalAST(lhs, z3, varASTMap), evalAST(rhs, z3, varASTMap))))
    
    val result = z3.check()
    
    z3.delete()
    cfg.delete()
    if (result isDefined) !result.get
    else true
  }
  
  def isSatisfiable(clexp:CLExp) : Boolean = {
    
    val cfg = new Z3Config
    val z3 = new Z3Context(cfg)
    val intSort:Z3Sort = z3.mkIntSort
    
    val varSet = getVarSet(clexp)
    val varASTMap = varSet.foldLeft(Map[String, Z3AST]())((map, v) => {
      map + (v -> z3.mkConst(z3.mkStringSymbol(v), intSort))
    })
    
    z3.assertCnstr(z3.mkEq(evalAST(clexp, z3, varASTMap), z3.mkTrue()))
    
    val result = z3.check()
    
    z3.delete()
    cfg.delete()
    if (result isDefined) result.get
    else true
  }
  
  def isValid(clexp:CLExp) : Boolean = {
    
    val cfg = new Z3Config
    val z3 = new Z3Context(cfg)
    val intSort:Z3Sort = z3.mkIntSort
    
    val varSet = getVarSet(clexp)
    val varASTMap = varSet.foldLeft(Map[String, Z3AST]())((map, v) => {
      map + (v -> z3.mkConst(z3.mkStringSymbol(v), intSort))
    })
    
    z3.assertCnstr(z3.mkNot(z3.mkEq(evalAST(clexp, z3, varASTMap), z3.mkTrue())))
    
    val result = z3.check()
    
    z3.delete()
    cfg.delete()
    if (result isDefined) !result.get
    else true
  }
}
