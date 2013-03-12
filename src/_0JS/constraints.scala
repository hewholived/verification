package _0JS
package CL

import HelperTypeAliases.VariableName

trait CLExp {
  override def toString() = this match {
    case CLNum(n) => n.toString()
    case CLVar(v) => v._1
    case CLBinop(e1, e2, op) => {
      "( " + e1.toString() + " " + (op match {
        case CLPlus => "+"
        case CLMinus => "-"
        case CLTimes => "*"
        case CLEquals => "="
        case CLNotEquals => "!="
        case CLLessEquals => "<="
        case CLGreaterEquals => ">="
        case CLLess => "<"
        case CLGreater => ">"
        case CLImplies => "=>"
        case CLAnd => "&&"
        case CLOr => "||"
      }) + " " + e2.toString() + " )"
    }
    case CLUnop(e, op) => "( " + (op match {
      case CLLogNot => "!"
    }) + e.toString() + " )"
    case CLNotJSVar(v) => "JSVar:" + v.name
    case CLTrue => "true"
    case CLFalse => "false"
  }
  
  def &&(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLAnd)
  }
  
  def implies(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLImplies)
  }
  
  def EQ(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLEquals)
  }
  
  def <(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLLess)
  }
  
  def >=(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLGreaterEquals)
  }
  
  def >(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLGreater)
  }
  
  def LEQ(rhs: CLExp) : CLExp = {
    CLBinop(this, rhs, CLLessEquals)
  }
  
  def unary_! : CLExp = CLUnop(this, CLLogNot)
}
case class CLNum(n: BigInt) extends CLExp
case class CLVar(v: VariableName) extends CLExp
case class CLBinop(e1: CLExp, e2: CLExp, op: CLBOP) extends CLExp
case class CLUnop(e1: CLExp, op: CLUOP) extends CLExp
case class CLNotJSVar(v: Variable) extends CLExp
case object CLTrue extends CLExp
case object CLFalse extends CLExp

trait CLUOP
case object CLLogNot extends CLUOP

trait CLBOP
case object CLPlus extends CLBOP
case object CLMinus extends CLBOP
case object CLTimes extends CLBOP
case object CLEquals extends CLBOP
case object CLNotEquals extends CLBOP
case object CLLessEquals extends CLBOP
case object CLGreaterEquals extends CLBOP
case object CLLess extends CLBOP
case object CLGreater extends CLBOP
case object CLImplies extends CLBOP
case object CLAnd extends CLBOP
case object CLOr extends CLBOP
