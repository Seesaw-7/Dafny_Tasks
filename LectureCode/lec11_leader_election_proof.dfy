//--------------- Proof

ghost predicate Between(start:nat, mid:nat, end:nat) {
  if start < end then 
    start < mid <= end
  else 
    mid > start || mid <= end
}

ghost predicate ChordDominates(c:Constants, v:Variables) {

}

ghost predicate Inv(c: Constants, v:Variables){
  && Safety(c, v)
}

lemma InvImpliesSafety(c: Constants, v:Variables)
  requires Inv(c,v)
  ensures Safety(c,v) {

}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v) {
}

lemma NextPreservesInv(c:Constants, v:Variables, v':Variables)
 requires Inv(c,v)
 requires Next(v, v')
 ensures Inv(c, v') {

}