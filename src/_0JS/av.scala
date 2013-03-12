package _0JS

import HelperTypeAliases._
import CL._

// An abstract value is made up of a name and associated constraints with that name
case class AV(v: VariableName, c: Set[CLExp])
