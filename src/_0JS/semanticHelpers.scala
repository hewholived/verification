package _0JS

import scala.collection.mutable.{Map => MMap}
import HelperTypeAliases._
import HelperObjects._
import CL._

object FreshIntGenerator {
  private var count: BigInt = 0

  def apply(): BigInt = {
    count += 1
    count
  }
}

object SemanticHelpers {

  def inject(e: AST) = {
    val in = new CollectIn()
    val out = new CollectOut()
    // TODO: In this env, add the default one
    val env = Env().addLQs(Set(LQMarketPlace.VGreaterThan0, LQMarketPlace.VLessThan0,  LQMarketPlace.VEquals0, LQMarketPlace.VLessEquals0, LQMarketPlace.VGreaterEquals0))
    //val env = Env().addLQs(Set(LQMarketPlace.zeroLessEqThanV, LQMarketPlace.zeroGreaterThanV))
    //val env = Env().addLQs(Set(LQMarketPlace.zeroLessEqThanV))
    val sto = Store()
    (Config(e, env, sto), in, out)
  }

  def alloc(av: AV,
            s: Store,
            termId: BigInt,
            pos: Int,
            env: Env): (AbstractAddress, Store) = {
    val address = (termId, pos)
    (address, s.alloc(address, av, env))
  }

  def alloc(av: List[AV],
            s: Store, 
            termId: BigInt, 
            pos: List[Int],
            env: Env): (List[AbstractAddress], Store) = {
    //require(av.length == pos.length)
    val (absAdds, sto1) = (av zip  pos).foldLeft((List[AbstractAddress](), s))(
      (acc: (List[AbstractAddress], Store), e: (AV, Int)) => {
        val (absAdd, newSto) = alloc(e._1, acc._2, termId, e._2, env)
        (absAdd::acc._1, newSto)
      })
    (absAdds.reverse, sto1)
  }

  def evalExps(es: List[AST],
               env: Env,
               sto: Store,
               in: CollectIn,
               out: CollectOut): (List[AV], Store) = {
    def evalExpsR(es: List[AST],
                  avs: List[AV], env: Env,
                  sto: Store): (List[AV], Store) = {
      es match {
        case h::t => {
          val (av, stoPrime) = Evaluator.eval(h, env, sto, in, out)
          evalExpsR(t, av::avs, env, stoPrime)
        }
        case Nil => (avs.reverse, sto)
      }
    }
    evalExpsR(es, Nil, env, sto)
  }

  def addToEnv(vars: List[Variable], addrs: List[AbstractAddress], env: Env) = {
    require(vars.length == addrs.length)
    (vars zip addrs).foldLeft(env)(_ + _)
  }

  def genLQs(xs: Seq[Variable]) = {
    xs.flatMap((star: Variable) =>
      Set(LQMarketPlace.starLessThanV(CLNotJSVar(star)),
          LQMarketPlace.vLessThanStar(CLNotJSVar(star)),
          LQMarketPlace.vGreaterEqStar(CLNotJSVar(star)))).toSet
  }

  def replaceNotJSVars(term: CLExp, env: Env, sto: Store): CLExp = {
    term match {
      case CLNum(n) => term
      case CLVar(v) => term
      case CLBinop(e1, e2, op) => CLBinop(replaceNotJSVars(e1, env, sto), replaceNotJSVars(e2, env, sto), op)
      case CLUnop(e1, op) => CLUnop(replaceNotJSVars(e1, env, sto), op)
      case CLNotJSVar(v) => CLVar(sto(env(v)).v)
      case CLTrue => CLTrue
      case CLFalse => CLFalse
    }
  }
  
  def freshVariableName:VariableName = ("_" + FreshIntGenerator().toString, FreshIntGenerator(), 0)

  def repeat[A](n: Int, item: A): List[A] =
    (0 to (n-1)).map(_ => item).toList
    
  def transformedCLExp(c:CLExp, oldName:VariableName, varName:VariableName) :CLExp = {
    c match {
      case CLNum(n) => c
      case CLVar(v) => v match {
        case `oldName` => CLVar(varName)
        case _       => c
      }
      case CLBinop(e1, e2, op) => CLBinop(transformedCLExp(e1, oldName, varName), transformedCLExp(e2, oldName, varName), op)
      case CLUnop(e1, op) => CLUnop(transformedCLExp(e1, oldName, varName), op)
      case CLNotJSVar(v) => c
      case CLTrue => CLTrue
      case CLFalse => CLFalse
    }
  }
    
  def renameVar(x:Variable, varName:VariableName, env:Env, store:Store): Store = {
    
    def renamed(av:AV):AV = {
      val oldName = store(env(x)).v
      
      if (av.v == oldName) {
        AV(varName, av.c.map(transformedCLExp(_, oldName, varName)))
      }
      else {
        AV(av.v, av.c.map(transformedCLExp(_, oldName, varName)))
      }
    }
    
    val adrs = env.env.values
    
    adrs.foldLeft(store)((sto, a) => {
      sto.strong(a, renamed(sto(a)), env)
    })
  }
  
  def isNamePresentInCLExp(lq:CLExp, name:VariableName): Boolean = {
    lq match {
      case CLNum(n) => false
      case CLVar(v) => v match {
        case `name` => true
        case _       => false
      }
      case CLBinop(e1, e2, op) => isNamePresentInCLExp(e1, name) || isNamePresentInCLExp(e2, name)
      case CLUnop(e1, op) => isNamePresentInCLExp(e1, name)
      case CLNotJSVar(v) => false
      case CLTrue => false
      case CLFalse => false
    }
  }
  
  def normalizeStore(oldVar:VariableName, elimCondition:CLExp, sto:Store, env:Env): Store = {
    
    def refineVar(x:Variable, sto:Store): Store = {
      val oldVal = sto(env(x)) 
      val varname = oldVal.v
      val cSet = oldVal.c
      
      val potentialLQs = env.lqs.map((f: LQFunction) => replaceNotJSVars(f(CLVar(varname)), env, sto)) --  
                         Set(CLVar(varname) < CLVar(varname), CLVar(varname) >= CLVar(varname), CLVar(varname) EQ CLVar(varname))
                         
      val constraint = getConjunction(cSet)
      val precedent = constraint && elimCondition
      
      val stickers = potentialLQs.filter((lq: CLExp) => Z3Solver.Z3Oracle(precedent, lq))
      
      val rhs = AV(varname, stickers)
      sto.strong(env(x), rhs, env)
    }
    val variables = env.env.keys
    variables.foldLeft(sto)((store, x) => {
      if (isNamePresentInCLExp(getConjunction(sto(env(x)).c), oldVar)) refineVar(x, store)
      else store
    })
  }
  
  def getCLop(op:CompBop): CLBOP = op match {
    case Equal => CLEquals
    case Neq => CLNotEquals
    case Gt => CLGreater
    case Lt => CLLess
    case Lte => CLLessEquals
    case Gte => CLGreaterEquals
  }
  
  def mergeStores(sto1:Store, sto2:Store, env:Env) : Store = {
    
    def mergeVar(x:Variable, sto1:Store, sto2:Store) : Store = {
      val av1 = sto1(env(x))
      val av2 = sto2(env(x))
      
      val stickers = av1.c intersect av2.c
      
      val rhs = AV(av1.v, stickers)
      sto1.strong(env(x), rhs, env)
    }
    
    val variables = env.env.keys
    variables.foldLeft(sto1)((store, x) => mergeVar(x, store, sto2))
  }
  
  def getConjunction(cSet: Set[CLExp]) : CLExp = {
    val defaultValue: CLExp = CLTrue
    cSet.foldLeft(defaultValue)((acc: CLExp, e: CLExp) => acc && e)
  }
  
  def validateAssumption(env: Env, elimCondition: CLExp, finalStickers: Set[CLExp], newv:VariableName, oldv:VariableName): Env = {
    getConjunction(env.assumptions.toSet) match {
      case assumption if (isNamePresentInCLExp(assumption, newv)) => {
        val prec = transformedCLExp(assumption, newv, oldv) 
        if( Z3Solver.Z3Oracle(prec && elimCondition && getConjunction(finalStickers), assumption)) env
        env remAssumption
      }
      case _ => env
    }
  }
  
  def areStoresEqual(sto1:Store, sto2:Store, env: Env): Boolean = {
    val variables = env.env.keys
    variables.forall((x) => sto1(env(x)) == sto2(env(x)))
  }

}