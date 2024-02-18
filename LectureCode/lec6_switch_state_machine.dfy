datatype SwitchState = On | Off

datatype Variables =
  Variables(switch:SwitchState)

predicate Init(v:Variables) {
  v.switch == Off
}

predicate Activate(v:Variables, v':Variables) {
  v'.switch == On
}

predicate Deactivate(v:Variables, v':Variables) {
  v'.switch == Off
}

predicate Toggle(v:Variables, v':Variables) {
  v'.switch != v.switch
}

predicate Next(v:Variables, v':Variables) { //Keeps all valid state transitions
  || Activate(v, v')
  || Deactivate(v, v')
  || Toggle(v, v')
}
