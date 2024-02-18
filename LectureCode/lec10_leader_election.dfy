datatype Constants = Constants(ids:seq<int>){
  ghost predicate UniqueIDs(){
    forall i:nat, j:nat |
      && i < |ids|
      && j < |ids|
      && ids[i] == ids[j]
      :: i == j
  }

  ghost predicate WellFormed(){
    && UniqueIDs()
    && |ids| > 0
  }

  ghost predicate ValidIndx(idx:nat){
    idx < |ids|
  }

  ghost function NextIdx(idx:nat) : nat {
    if idx == |ids| - 1 then 0 else idx+1 // another definition of modulo
  }
}

datatype Variables = Variables(max_heard_ids:seq<int>){
  ghost predicate WellFormed(c: Constants){
    && c.WellFormed()
    && |c.ids| == |max_heard_ids|
  }
}

ghost predicate Init(c:Constants, v:Variables){
  && v.WellFormed(c)
  && (forall i:nat | c.ValidIndx(i) :: v.max_heard_ids[i] == -1)
}

ghost function max(a: int, b: int) : (ret: int)
  ensures ret>=a && ret >=b
  ensures ret == a || ret == b
{
  if a > b then a else b
}

ghost predicate SendMessage(c:Constants, v:Variables, v':Variables, idx:nat){
  && v.WellFormed(c)
  && c.ValidIndx(idx)
  &&  var msg:= max(v.max_heard_ids[idx], c.ids[idx]);
  var value := max(v.max_heard_ids[c.NextIdx(idx)],msg);
  v' == v.(max_heard_ids := v.max_heard_ids[c.NextIdx(idx) := value])
}

datatype Step =
  | SendMessageStep(idx:nat)


ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step:Step){
  match step
  case SendMessageStep(idx) => SendMessage(c,v,v',idx)
}

ghost predicate IsLeader(idx:nat, v:Variables, c:Constants){
  && v.WellFormed(c)
  && c.ValidIndx(idx)
  && c.ids[idx] == v.max_heard_ids[idx]
}

ghost predicate Safety(c:Constants, v:Variables){
  forall i:nat, j:nat |
    && c.ValidIndx(i)
    && c.ValidIndx(j)
    && IsLeader(i, v, c)
    && IsLeader(i, v, c)
    :: i == j

}