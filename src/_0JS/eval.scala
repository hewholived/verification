package _0JS

import HelperTypeAliases._
import SemanticHelpers._
import HelperObjects._
import CL._

object Evaluator {

  def eval(x: (Config, CollectIn, CollectOut)): (AV, Store) = {
    eval(x._1, x._2, x._3)
  } 

  def eval(e: AST, 
           newenv: Env, 
           newsto: Store, 
           in: CollectIn,
           out: CollectOut): (AV, Store) = {
    eval(Config(e, newenv, newsto), in, out)
  }

  def eval(config: Config, in: CollectIn, out: CollectOut): (AV, Store) = {

    // closes over in and out
    def evalExps(es: List[AST],
                 env: Env,
                 sto: Store): (List[AV], Store) = {
      SemanticHelpers.evalExps(es, env, sto, in, out)
    }

    // the inner eval -- closes over in and out
    def eval(e: AST, newenv: Env, newsto: Store): (AV, Store) = {

      /*val doMap = e.isInstanceOf[Seq] || e.isInstanceOf[MethodCall] ||
        e.isInstanceOf[While] || e.isInstanceOf[Throw] ||
        e.isInstanceOf[LabelExp] || //remove throw and break?
        e.isInstanceOf[Break] || e.isInstanceOf[HandleEvts]*/
      //val doMap = e.isInstanceOf[While] || e.isInstanceOf[Sequence]
      val doMap = false

//      val (env, sto) = if(doMap) {
//        val (doMore, envTmp, stoTmp) = in.collect(e.id, newenv, newsto, context, sc)
//        if (!doMore)
//          return out.collect(e.id, context, sc, stoTmp)
//        //        out.collect(true, e.id, BOTTOM, env_tmp, sto_tmp, context, sc)
//        (envTmp, stoTmp)
//      } else {
//        (newenv, newsto)
//      }
      val (env, sto) = (newenv, newsto)

      e match {
        case Program(t) => eval(t, env, sto)
        // VAL
        case Num(n) => {
          // num | num = n
          val name = ("num", e.id, 0)
          val constraint = CLVar(name) EQ CLNum(n.toInt) 
          out.collect(doMap, e.id, AV(name, Set(constraint)), env, sto)
        }

        case Bool(b) => throw notHandled("boolean")

        case Str(s) => throw notHandled("string")
        
        case NotUnit() => out.collect(doMap, 0, AV(freshVariableName, Set(CLTrue)), env, sto)

        // VAR
        case x@Variable(_) => {
          val av: AV = sto(env(x)) // latest value of x in store
          out.collect(doMap, x.id, av, env, sto)
        }

        // SEQ, SEQ-J
        case s@Sequence(e) => {
          require(e.nonEmpty)
          val (avs, sto1) = evalExps(e.toList, env, sto)
          out.collect(doMap, s.id, avs.last, env, sto1)
        }

        // BLOCK
        case b@Block(xs, e) => {
          val defaultVals:List[AV] = xs.map((x) => BOTTOM((x.name, x.id, 0)))
          val (a, sto1) = alloc(defaultVals, sto, b.id, List.range(0, xs.length), env)
          val lqs = genLQs(xs)
          val env1 = addToEnv(xs.toList, a, env).addLQs(lqs)
          val (av, sto2) = eval(e, env1, sto1)
          out.collect(doMap, b.id, av, env, sto2)
        }
        
        // binary operators
        case BinOp(_:Num, Mul, _:Exp) | BinOp(_:Exp, Mul, _:Num) | BinOp(_:Exp, Add, _:Exp) | BinOp(_:Exp, Sub, _:Exp) => {
          val binop = e.asInstanceOf[BinOp]
          val (e1, e2, op) = (binop.e1, binop.e2, binop.op)
          val (av1, sto1) = eval(e1, env, sto)
          val (av2, sto2) = eval(e2, env, sto1)
          val newv:VariableName = freshVariableName
          
          // for each lq in env
          val potentialLQs = env.lqs.map((f: LQFunction) => replaceNotJSVars(f(CLVar(newv)), env, sto2))
          // newv = av.v && av.c
          
          val clOP = op match {
            case Add => CLPlus
            case Sub => CLMinus
            case Mul => CLTimes
            case _ => throw notImplemented("All the operators")
          }

          // add stuff from env to the precedent?
          val av1_constr = getConjunction(av1.c)
          val av2_constr = getConjunction(av2.c)
          val precedent = (CLVar(newv) EQ CLBinop(CLVar(av1.v), CLVar(av2.v), clOP)) &&  av1_constr && av2_constr && getConjunction(env.assumptions.toSet)

          // find the ones that stick
          val stickers = potentialLQs.filter((lq: CLExp) => Z3Solver.Z3Oracle(precedent, lq))
          
          val rhs = AV(newv, stickers)

          out.collect(doMap, e.id, rhs, env, sto2)
        }
        
        case BinOp(e1, Mul, e2) => {
          val (av1, sto1) = eval(e1, env, sto)
          val (av2, sto2) = eval(e2, env, sto1)
          
          out.collect(doMap, e.id, IntTheory.solveMul(av1, av2, env.assumptions.toSet), env, sto2)
        }

        case If(guard, e1, e2) => {
          
          guard match {
            case BinOp(lhs:Exp, op:CompBop, rhs:Exp) => {
              val (av1, sto1) = eval(lhs, env, sto)
              val (av2, sto2) = eval(rhs, env, sto1)
              
              val tConstr = CLBinop(CLVar(av1.v), CLVar(av2.v), getCLop(op))
              val fConstr = !tConstr
              val av1_constr = getConjunction(av1.c)
              val av2_constr = getConjunction(av2.c) 
              val tGuardConstr = tConstr && av1_constr && av2_constr && getConjunction(env.assumptions.toSet)
              val fGuardConstr = fConstr && av1_constr && av2_constr && getConjunction(env.assumptions.toSet)
              
              //Check whether trueGuard or falseGuard is satisfiable. If you find either one of these not satisfiable do not evaluate that branch.
              lazy val (avTrue, sto3)  = eval(e1, env extend tGuardConstr, sto2)
              lazy val (avFalse, sto4) = eval(e2, env extend fGuardConstr, sto2)

              (Z3Solver.isSatisfiable(tGuardConstr), Z3Solver.isSatisfiable(fGuardConstr)) match {
                case (true, true)  => out.collect(doMap, e.id, avTrue, env, mergeStores(sto3, sto4, env))
                case (true, false) => out.collect(doMap, e.id, avTrue, env, sto3)
                case (false, true) => out.collect(doMap, e.id, avFalse, env, sto4)
                case _ => throw notImplemented("This cannot happen!")
              }
            }
            case _ => throw notImplemented("if with non-relational gaurd")
          }
        }

        // WHILE-T, WHILE-TF-J1, WHILE-T-J2, WHILE-F
        case w@While(guard, e) => {
          guard match {
            case BinOp(lhs:Exp, op:CompBop, rhs:Exp) => {
              
              var stoS = sto
              var sto3 = sto
              var sto4 = sto
              
              do {
                stoS = mergeStores(sto3, sto4, env)
                val (av1, sto1) = eval(lhs, env, stoS)
                val (av2, sto2) = eval(rhs, env, sto1)
              
                val av1Constr = getConjunction(av1.c)
                val av2Constr = getConjunction(av2.c) 
                val tConstr = CLBinop(CLVar(av1.v), CLVar(av2.v), getCLop(op))
                val fConstr = !tConstr
                val tGuardConstr = tConstr && av1Constr && av2Constr && getConjunction(env.assumptions.toSet)
                val fGuardConstr = fConstr && av1Constr && av2Constr && getConjunction(env.assumptions.toSet)

                val isTrue = Z3Solver.isSatisfiable(tGuardConstr)
                val isFalse = Z3Solver.isSatisfiable(fGuardConstr)
                
                lazy val (avBody, stoB) = eval(e, env extend tGuardConstr, stoS)
                sto3 = if (isTrue) stoB else stoS
                sto4 = if (isFalse) stoS else stoB
                
                //println(isTrue, isFalse)
                
              } while(!areStoresEqual(mergeStores(sto3, sto4, env), stoS, env))
              
              val (r_av1, r_sto1) = eval(lhs, env, stoS)
              val (r_av2, r_sto2) = eval(rhs, env, r_sto1)
              
              val r_av1Constr = getConjunction(r_av1.c)
              val r_av2Constr = getConjunction(r_av2.c) 
              val r_fConstr = !CLBinop(CLVar(r_av1.v), CLVar(r_av2.v), getCLop(op))
              
              
              val r_fGuardConstr = r_fConstr && r_av1Constr && r_av2Constr && getConjunction(env.assumptions.toSet)
              
              env addAssumption r_fGuardConstr 
              out.collect(doMap, e.id, AV(freshVariableName, Set(CLTrue)), env, stoS)
            }
            case _ => throw notImplemented("while with non-relational gaurd")
          }
        }

        // ASN, ASN-J
        case asn@Assign(x, e) => {
          val (av, sto1) = eval(e, env, sto)
          
          //fetch the variable name present in the current store
          val newv:VariableName = sto(env(x)).v 
          
          //rename all the prev values of xv to xv$$$
          val oldv:VariableName = (x.name + "$$$", asn.id, 0)
          
          val sto2 = renameVar(x, oldv, env, sto1)

          // for each lq in env
          val potentialLQs = env.lqs.map((f: LQFunction) => replaceNotJSVars(f(CLVar(newv)), env, sto2)) - (CLVar(newv) EQ CLVar(newv))
          // newv = av.v && av.c

          val av_constr = getConjunction(av.c)
          val retConstr = transformedCLExp(av_constr, newv, oldv)
          // add stuff from env to the precedent?
          val precedent = (CLVar(newv) EQ CLVar(av.v)) && retConstr && transformedCLExp(getConjunction(env.assumptions.toSet), newv, oldv)

          // find the ones that stick
          val stickers = potentialLQs.filter((lq: CLExp) => Z3Solver.Z3Oracle(precedent, lq))

          val elimCondition = getConjunction(stickers.filter((lq:CLExp) => isNamePresentInCLExp(lq, oldv)))
          
          val finalStickers = stickers.filterNot((lq:CLExp) => isNamePresentInCLExp(lq, oldv))

          val rhs = AV(newv, finalStickers)

          // always strong updates? for simple language, yes.
          val sto3 = sto2.strong(env(x), rhs, env)
          
          val sto4 = normalizeStore(oldv, elimCondition, sto3, env)
          
          val env1 = validateAssumption(env, elimCondition, finalStickers, newv, oldv)
          
          //println(sto4)
          
          out.collect(doMap, asn.id, av, env1, sto4)
        }
        
        case Assert(guard) => {
          guard match {
            case BinOp(lhs:Exp, op:CompBop, rhs:Exp) => {
              val (av1, sto1) = eval(lhs, env, sto)
              val (av2, sto2) = eval(rhs, env, sto1)
              
              val av1_constr = getConjunction(av1.c)
              val av2_constr = getConjunction(av2.c) 
              val constr = !(CLBinop(CLVar(av1.v), CLVar(av2.v), getCLop(op)))
              val assertConstr = constr && av1_constr && av2_constr && getConjunction(env.assumptions.toSet)
              
              if (Z3Solver.isSatisfiable(assertConstr)) println("Assertion failed!")
              else println("Assertion passed!")
              
              out.collect(doMap, e.id, AV(freshVariableName, Set(CLTrue)), env, sto)
            }
            case _ => throw notImplemented("assert with non-relational gaurd")
          }
        }
        
        case Out(e) => {
          println(e)
          out.collect(doMap, 0, AV(freshVariableName, Set(CLTrue)), env, sto)
        }
        case a@_ => 
          throw notImplemented("Rest of AST" + a)
      } // match expression
    }

    eval(config.e, config.env, config.sto)
  }
}