package _0JS

import scala.collection.mutable.{Set => MSet}
import HelperTypeAliases._
import SemanticHelpers.getConjunction
import CL._

case class Config(e: AST, env: Env, sto: Store)

// abstract semantic domains
case class Env(env: Map[Variable, AbstractAddress] = Map(), lqs: Set[LQFunction] = Set(), assumptions: MSet[CLExp] = MSet(CLTrue)) {
  def has(x: Variable) = env.contains(x)

  def apply(x: Variable) = {
    if (has(x)) env(x)
    else {
        throw undefined("Variable: " + x + " not in environment")
      }
  }

  def get(x: Variable) = env.get(x)

  def +(pair: (Variable, AbstractAddress)) = Env(env + pair, lqs, assumptions)

  def addLQs(fs: Set[LQFunction]) = Env(env, lqs ++ fs, assumptions)
  
  def extend(constr: CLExp) = Env(env, lqs, assumptions + constr)
  
  def remAssumption() = {
    assumptions.clear()
    assumptions += CLTrue
    this
  }
  
  def addAssumption(constr: CLExp) = {
    assumptions += constr
  }
}

case class Store(sto: Map[AbstractAddress, AV] = Map(),
                 weak_set : Set[AbstractAddress] = Set()) {
  def has(x: AbstractAddress) = sto.contains(x)
  
  override def toString() = {
    sto.values.foldLeft("")((ret, av) => ret + "( " + av.v._1 + " | " + getConjunction(av.c).toString + " )") 
  }

  def apply(x: AbstractAddress) = {
    if (has(x)) sto(x)
    else throw undefined( "Abstract Address: " + x + " not in store")
  }

  def get(x: AbstractAddress) = sto.get(x)

  //this is *always* a weak update, and should be used by
  //the allocation function, for example.  It will mark
  //an address as being used twice (unsafe) if necessary.
  def alloc(addr:AbstractAddress, av:AV, env: Env) = {
    if (sto.keySet contains addr)
      Store(sto + ((addr, Join(av, sto(addr), env))), weak_set + addr)
    else
      Store(sto + ((addr,av)), weak_set)
  }

  //this always does a weak update.
  //it requires that the address has already been
  //allocated into the store.  Not to be used by allocation
  //functions!!
  def weak(addr:AbstractAddress, av:AV, env: Env) = {
    assert (sto.keySet contains addr)
    Store(sto + ((addr, Join(av, sto(addr), env))), weak_set)
  }

  //this tries to do a strong update, if it's safe for a
  //non-allocation function.  The assumption is that the
  //address is already allocated into the store.
  def strong(addr:AbstractAddress, av:AV, env: Env) = {
    assert (sto.keySet contains addr)
    if (weak_set contains addr)
      weak(addr, av, env)
    else
      Store(sto + ((addr,av)), weak_set)
  }
}