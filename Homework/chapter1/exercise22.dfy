//#title Binary Tree Search
//#desc Implement search in a binary tree and prove it works.
//#desc Practice with proof diagnosis.

include "exercise21.dfy"
//#extract exercise21.template solution exercise21.dfy

// This exercise builds on exercise21 (so make sure you have completed
// that one, too). If in doubt about your solution to exercise21, contact 
// an instructor during office hours to make sure you're on the right path. 

predicate SequenceIsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

lemma SortedTreeMeansSortedSequence(tree:Tree)
    requires IsSortedTree(tree)
    ensures SequenceIsSorted(TreeAsSequence(tree))
{
}

method FindInBinaryTree(tree:Tree, needle:int) returns (found:bool)
    requires IsSortedTree(tree)
    ensures found <==> needle in TreeAsSequence(tree)
{
/*{*/
    if tree == Nil{
        return false;
    }
    else{
        if tree.value == needle{
            return true;
        }
        else if tree.value < needle{
            SortedTreeMeansSortedSequence(tree.left);
            assert(forall x:int | x in TreeAsSequence(tree.left) :: x<= tree.value);
            var result := FindInBinaryTree(tree.right, needle);
            return result;
        }
        else {
            SortedTreeMeansSortedSequence(tree.right);
            assert(forall x:int | x in TreeAsSequence(tree.right) :: x>= tree.value);
            var result := FindInBinaryTree(tree.left, needle);
            return result;
        }
    }
    // var result := needle in TreeAsSequence(tree);
    // return result;
/*}*/
}
