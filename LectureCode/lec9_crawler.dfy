datatype Variables = Variables(y: int, isGoingNorth: bool)

ghost predicate Init(v: Variables){
  && v.y == 5
  && v.isGoingNorth == true
}

ghost predicate Flip(v:Variables, v':Variables){
  && v'.y + v.y == 0
  && v'.isGoingNorth != v.isGoingNorth
}

ghost predicate MoveNorth(v:Variables, v':Variables){
  && v.(y:=v.y+1) == v'
  && v.isGoingNorth
}

ghost predicate MoveSouth(v:Variables, v':Variables){
  && v.(y:=v.y+1) == v'
  && v.isGoingNorth
}

// The following is re-written in JNF
// ghost predicate Next(v: Variables, v': Variables){
//   || MoveNorth(v,v')
//   || MoveSouth(v,v')
//   || Flip(v,v')
// }

datatype Step =
  | Flip
  | MoveNorth
  | MoveSouth

ghost predicate NextStep(v:Variables, v':Variables, step:Step){
  match step
  case Flip => Flip(v, v')
  case MoveNorth => MoveNorth(v, v')
  case MoveSouth => MoveSouth(v, v')
}

ghost predicate Next(v: Variables, v': Variables){
  || MoveNorth(v,v')
  || MoveSouth(v,v')
  || Flip(v,v')
}

ghost predicate Safety(v: Variables){ // safety only cares whether a state is safe or not (cares about one state only)
  // However, when it’s y>3, it cannot go south
  || v.y > 3
  || v.y < -3
}

ghost predicate Inv(v: Variables){
  && Safety(v)
  && (v.isGoingNorth ==> v.y > 3)
  && (!v.isGoingNorth ==> v.y < -3)
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Inv(v)
  ensures forall v, v' | Inv(v) && Next(v,v'):: Inv(v')
  ensures forall v | Inv(v) :: Safety(v){
}
