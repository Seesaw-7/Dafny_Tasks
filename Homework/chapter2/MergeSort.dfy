//#title Merge Sort
//#desc More specification practice.

// Implement a merge sort that guarantees the result is sorted.
// merge() should merge its two sorted inputs into a sorted output.
// merge_sort picks a pivot, recursively merge_sort()s the subsequences,
// and then uses merge() to put them back together. We've provided
// signatures for merge and merge_sort to get you started.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

/*{*/
lemma MultisetSeqAppend(seqint:seq<int>, index:nat)
  requires index < |seqint| 
  ensures multiset(seqint[..index]) + multiset([seqint[index]]) == multiset(seqint[..index+1])
{
  assert seqint[..(index+1)] == seqint[..index] + [seqint[index]];
  assert multiset(seqint[..(index+1)]) == multiset(seqint[..index] + [seqint[index]]);
  assert multiset(seqint[..(index+1)]) == multiset(seqint[..index]) + multiset([seqint[index]]);  
}
/*}*/

method merge_sort(input:seq<int>) returns (output:seq<int>)
/*{*/
  ensures IsSorted(output)  
  ensures multiset(output) == multiset(input)  
/*}*/
{
/*{*/
  if |input| <= 1 {
    return input;
  } else {
    var pivot := |input| / 2;
    var left := merge_sort(input[..pivot]);
    var right := merge_sort(input[pivot..]);
    output := merge(left, right); 
    assert input == input[..pivot] + input[pivot..];
    assert multiset(output) == multiset(left) + multiset(right);
    return output;
  }
/*}*/
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
/*{*/
  ensures IsSorted(output)  
  ensures multiset(output) == multiset(seqa) + multiset(seqb) 
/*}*/
{
/*{*/
  var result: seq<int> := [];
  var i := 0;
  var j := 0;
  while i < |seqa| || j < |seqb|
    invariant 0 <= i <= |seqa|
    invariant 0 <= j <= |seqb|
    decreases |seqa| + |seqb| - i - j 

    invariant |result| == i + j
    invariant forall x:int | x in seqa[..i] :: x in result
    invariant forall x:int | x in seqb[..j] :: x in result
    invariant if i+j > 0 then
           if i < |seqa| && j < |seqb| then result[i+j-1] <= seqa[i] && result[i+j-1] <= seqb[j]
           else if i < |seqa| && j == |seqb| then result[i+j-1] <= seqa[i]
           else if i == |seqa| && j < |seqb| then result[i+j-1] <= seqb[j]
           else true
           else true
    invariant IsSorted(result)

    invariant multiset(result) == multiset(seqa[..i]) + multiset(seqb[..j])
  { 
    var old_result := result;
    var indicator:int := 0;
    if i < |seqa| && (j >= |seqb| || seqa[i] <= seqb[j]) {
      result := result + [seqa[i]];
      MultisetSeqAppend(seqa, i);
      i := i + 1;
      indicator := 1;
    } else  {
      result := result + [seqb[j]];
      MultisetSeqAppend(seqb, j);
      j := j + 1;
      indicator := 2;
    } 
  }

  assert seqa == seqa[..i];
  assert seqb == seqb[..j];
  assert multiset(result) == multiset(seqa) + multiset(seqb);
  return result;
/*}*/
}
