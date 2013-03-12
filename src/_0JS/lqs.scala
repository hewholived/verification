package _0JS

import CL._

object LQMarketPlace {
  val VGreaterThan0  = (v: CLVar) => CLBinop(v, CLNum(0), CLGreater)
  val VLessThan0 = (v: CLVar) => CLBinop(v, CLNum(0), CLLess)
  val VEquals0 = (v: CLVar) => CLBinop(v, CLNum(0), CLEquals)
  val VGreaterEquals0 = (v: CLVar) => CLBinop(v, CLNum(0), CLGreaterEquals)
  val VLessEquals0 = (v: CLVar) => CLBinop(v, CLNum(0), CLLessEquals)
  

  def starLessThanV(star: CLNotJSVar): ((CLVar) => CLExp) = {
    (v: CLVar) => CLBinop(star, v, CLLess)
  }

  def vLessThanStar(star: CLNotJSVar): ((CLVar) => CLExp) = {
    (v: CLVar) => CLBinop(v, star, CLLess)
  }
  
  def vGreaterEqStar(star: CLNotJSVar): ((CLVar) => CLExp) = {
    (v: CLVar) => CLBinop(v, star, CLGreaterEquals)
  }
}