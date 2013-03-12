package _0JS
import CL._

package object HelperTypeAliases {
  // variable name, location, position
  type VariableName = (String, BigInt, Int)
  type AbstractAddress = (BigInt, Int)
  type LQFunction = (CLVar) => CLExp
}
