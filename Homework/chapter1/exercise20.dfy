//#title Binary Search
//#desc Method implementation; writing a Hoare spec.

ghost predicate IsSorted(seqint:seq<int>) {
    forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// Write down the BinarySearch algorithm, which should return
// the index of the first element of the haystack that is >= to the needle.
// If the needle is present, this should be the index of the needle.
// If needle is bigger than every element, return the length of the
// sequence: It's not a valid index in the sequence, but it's bigger
// than the indices of all the elements that have smaller values.

lemma BinarySearch(haystack:seq<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack)
/*{*/
    ensures if |haystack| == 0 then index == 0
        else if needle > haystack[|haystack|-1] then index == |haystack|
        else && index < |haystack|
             && haystack[index] >= needle
             && if index > 0 then haystack[index - 1] < needle
                else true
/*}*/
{
/*{*/
    if |haystack| == 0 { return 0;}
    else if needle > haystack[|haystack|-1] {return |haystack|;}
    else if |haystack| == 1 {return 0;}      
    else {
        var i := |haystack| / 2;
        if haystack[i] < needle { 
            var result := BinarySearch(haystack[i..], needle); 
            return result + i;
            }
        else {
            var result := BinarySearch(haystack[..i], needle); 
            return result;}
    }
    // return 0;  // Replace me with an implementation.
/*}*/
}


