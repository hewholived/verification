package _0JS

import HelperTypeAliases._
import HelperObjects._
import SemanticHelpers._
import CL._
import CL.{CLTrue, CLExp, CLAnd, CLEquals}

object Join {
  def apply(av1: AV, av2: AV, env: Env): AV = {
    throw notImplemented("join")
//    val newv = (av1.v._1, av1.v._2, FreshIntGenerator())
//
//    val potentialLQs = env.lqs.map((f: LQFunction) => replaceNotJSVars(f(CLVar(newv)), env, sto))
//    // newv = av.v && av.c
//
//    // add stuff from env to the precedent?
//    val precedent1 = CLBinop(CLBinop(CLVar(newv), CLVar(av1.v), CLEquals), av1.c, CLAnd)
//    val precedent2 = CLBinop(CLBinop(CLVar(newv), CLVar(av2.v), CLEquals), av2.c, CLAnd)
//    val p1andp2 = CLBinop(precedent1, precedent2, CLAnd)
//
//    // find the ones that stick
//    val stickers = potentialLQs.filter((lq: CLExp) => Z3Solver.Z3Oracle(p1andp2, lq))
//
//    val defaultValue: CLExp = CLTrue
//    AV(newv, stickers.foldLeft(defaultValue)((acc: CLExp, e: CLExp) => CLBinop(acc, e, CLAnd)))
  }

  def apply(s1: Store, s2: Store, env: Env): Store = {
    val starting_weak = s1.weak_set ++ s2.weak_set
    val s1Only = s1.sto.keys.toSet -- s2.sto.keys.toSet
    val s2Only = s2.sto.keys.toSet -- s1.sto.keys.toSet
    val s1ands2 = s1.sto.keys.toSet ++ s2.sto.keys.toSet
    s1ands2.foldLeft(Store(Map(),starting_weak))((acc: Store, a: AbstractAddress) => {
      if (s1Only contains a)
        Store(acc.sto + (a -> s1(a)), acc.weak_set)
      else if (s2Only contains a)
        Store(acc.sto + (a -> s2(a)), acc.weak_set)
      else
        Store(acc.sto + (a -> Join(s1(a), s2(a), env)),acc.weak_set)
    })
  }

  def apply(e1: Env, e2: Env): Env  = {
    val e1Only = e1.env.keys.toSet -- e2.env.keys.toSet
    val e2Only = e2.env.keys.toSet -- e1.env.keys.toSet
    val e1ande2 = e1.env.keys.toSet ++ e2.env.keys.toSet
    val lqs = e1.lqs ++ e2.lqs
    e1ande2.foldLeft(Env().addLQs(lqs))((acc: Env, a: Variable) => {
      if (e1Only contains a) acc + (a -> e1(a))
      else if (e2Only contains a) acc + (a -> e2(a))
      else throw internalBug("Should not have reached here")
      //acc + (a -> Join(e1(a),e2(a)))
    })
  }

//  def apply(l: List[AV], env: Env): AV = {
//    l.foldLeft(BOTTOM)(
//      (acc: AV, v: AV) => {
//        Join(acc,v, env)
//      })
//  }
//
//  def apply(l: List[(AV, Store)], env: Env): (AV, Store) = {
//    l.foldLeft((BOTTOM, Store(Map(),Set())))(
//      (acc: (AV,  Store), e: (AV,  Store)) => {
//        (Join(acc._1, e._1, env), Join(acc._2, e._2, env))
//      }
//    )
//  }
}
