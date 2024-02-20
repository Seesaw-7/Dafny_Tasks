//#title Single-Server Lock Service Proof
//#desc A more realistic invariant proof of the previous chapter's lock
//#desc service.

// We provide a correct spec for the lock server here, but leave you
// to define the Safety property to be proven.
// You are welcome to prove correct your own model from chapter03,
// but note that may be too hard or too easy if your spec is broken.

// Copy your solution for chapter03/exercise03 into the current directory with
// this name:
include "../chapter3/Single-ServerLockServiceModel.dfy"
//#extract ../../chapter03-state-machines/exercises/exercise03.template solution chapter03-exercise03.dfy


/*{*/

/*}*/
ghost predicate Inv(c:Constants, v:Variables) {
/*{*/
  && v.WellFormed(c)
  && (|| (&& v.server == false 
          && (forall i:nat, j:nat |
                && c.ValidIndex(i) 
                && c.ValidIndex(j) 
                && v.clients[i] == true
                && v.clients[j] == true
                  :: i == j)
         )
      || (&& v.server == true
          && (forall i:nat |
                && c.ValidIndex(i)
                  :: v.clients[i] == false)
         )
     )
/*}*/
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(c:Constants, v:Variables, v':Variables)
  ensures Init(c, v) ==> Inv(c, v)
  ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
  ensures Inv(c, v) ==> Safety(c, v)
{
/*{*/
/*}*/
}