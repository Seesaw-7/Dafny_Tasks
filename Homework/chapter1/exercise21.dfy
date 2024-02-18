//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

include "UtilitiesLibrary.dfy"
import opened UtilitiesLibrary

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

/*{*/
// you should define your Tree datatype here.
datatype Tree = Node(value: int, left: Tree, right: Tree) | Nil()
/*}*/

// This lemma is here to guide you in defining the tree in a way
// that will help with the rest of the exercise.
lemma DatatypeCheck()
{
  var emptyTree := Nil;
  var littleTree := Node(9, Nil, Nil);
  var biggerTree := Node(10, littleTree, littleTree); // Note: not sorted
}

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// New syntax:  a function method is just like any other function, except it
// can be used in an "imperative" context (i.e., inside a method)

function TreeAsSequence(tree:Tree) : seq<int>
{
/*{*/   
    if tree == Nil then []
    else if && tree.left == Nil 
            && tree.right == Nil
            then [tree.value]
    else TreeAsSequence(tree.left) + [tree.value] + TreeAsSequence(tree.right)
/*}*/
}

// If this predicate is true about sorted sequences, then everything
// in seq1 is <= everything in seq2.
predicate SequencesOrderedAtInterface(seq1:seq<int>, seq2:seq<int>)
{
  if |seq1|==0 || |seq2|==0
  then true
  else Last(seq1) <= seq2[0]
}

predicate IsSortedTree(tree:Tree) {
/*{*/
    if tree == Nil then true
    else && IsSortedTree(tree.left)
         && IsSortedTree(tree.right)
         && SequencesOrderedAtInterface(TreeAsSequence(tree.left), [tree.value])
         && SequencesOrderedAtInterface([tree.value], TreeAsSequence(tree.right))
         // Replace me
/*}*/
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

datatype TreeSortedness = Unsorted | Empty | Bounded(low: int, high: int)

// Write a recursive implementation that checks if a tree
// is sorted by checking the children, then using TreeAsSequence
// on the children to confirm that both children stay on their
// respective sides of the pivot.
method CheckIfSortedTree(tree:Tree) returns (out: TreeSortedness)
    ensures IsSortedTree(tree) ==> !out.Unsorted?
    ensures IsSortedTree(tree) <== !out.Unsorted?
  /*{*/
    ensures if out.Bounded? then IsSortedTree(tree) else true
    ensures if out.Bounded? then |TreeAsSequence(tree)| > 0 else true
    ensures if out.Bounded? then TreeAsSequence(tree)[0] == out.low else true
    ensures if out.Bounded? then Last(TreeAsSequence(tree)) == out.high else true
    ensures if out.Empty? then tree == Nil else true
    ensures IsSortedTree(tree) ==> forall i:nat,j:nat | i<j<|TreeAsSequence(tree)| :: TreeAsSequence(tree)[i] <= TreeAsSequence(tree)[j]
  /*}*/
{
  /*{*/
  if tree == Nil {
    return Empty;}
  else {   
    var left := CheckIfSortedTree(tree.left);
    var right := CheckIfSortedTree(tree.right);

    if || left == Unsorted
       || right == Unsorted {
        return Unsorted;
    }
    else if left.Bounded? && right.Bounded? {
      if && left.high <= tree.value
         && right.low >= tree.value{
          return Bounded(left.low, right.high);
         }
      else{
        return Unsorted;
      }
    }
    else if left.Bounded? && right == Empty{
      if left.high > tree.value{
        return Unsorted;
      }
      else{
        return Bounded(left.low, tree.value);
      }
    }
    else if left == Empty && right.Bounded? {
      if right.low < tree.value {
        return Unsorted;
      }
      else{
        return Bounded(tree.value, right.high);
      }
    }
    else{
      return Bounded(tree.value, tree.value);
    }
  }
  // Implement this method. Feel free to make this a recursive method.
  /*}*/
}

