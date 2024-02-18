//#title IsSeqSorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsSeqSorted(intSeq:seq<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intSeq[..])
{
  /*{*/
  var i := 0;
  while(i < |intSeq|)
    invariant 0 <= i <= |intSeq|
    // invariant forall u:nat, k:nat| 
    //                       && k < i
    //                       && k<u<|intSeq|
    //                       :: intSeq[k] <= intSeq[u]
    // invariant forall k:nat | k<i :: forall u:nat | k<u<|intSeq| :: intSeq[k] <= intSeq[u]
    invariant forall k:nat | k<i :: !exists u:nat | k<u<|intSeq| :: intSeq[k] > intSeq[u]
  {
    var j := i + 1;
    while(j < |intSeq|)
      invariant i < j <= |intSeq|
      invariant forall k:nat | i<k<j :: intSeq[i] <= intSeq[k]
    {
      if intSeq[i] > intSeq[j]{
        return false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
  /*}*/
}
