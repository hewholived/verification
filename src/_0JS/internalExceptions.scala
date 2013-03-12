package _0JS

// use one of these exceptions within the ai

case class undefined(message: String) extends Exception(message)
case class notHandled(message: String) extends Exception(message)
case class internalBug(message: String) extends Exception(message)
case class notImplemented(message: String) extends Exception(message)
