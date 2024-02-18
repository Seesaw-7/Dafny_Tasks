//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

datatype Constants = Constants(
/*{*/ 
    numClients:nat
/*}*/
) {
  ghost predicate WellFormed() { true }
/*{*/
  ghost predicate ValidIndex(idx:nat){
    idx < numClients
  }
/*}*/
}

/*{*/
/*}*/

datatype Variables = Variables(
/*{*/ 
  server:bool,
  clients:seq<bool>
/*}*/
) {
  ghost predicate WellFormed(c: Constants) {
/*{*/
    |clients| == c.numClients
/*}*/
  }
}

ghost predicate Init(c:Constants, v:Variables) {
  && v.WellFormed(c)
/*{*/
  && v.server == true
  && forall x:bool | x in v.clients :: x == false
/*}*/
}

/*{*/
ghost predicate ValidSetup(c:Constants, v:Variables, v':Variables, clientIndex:nat){
    && v.WellFormed(c)
    && v'.WellFormed(c)
    && c.ValidIndex(clientIndex)
}


ghost predicate Acquire(c:Constants, v:Variables, v':Variables, clientIndex:nat){
    && ValidSetup(c, v, v', clientIndex) // It is not doing global safety check, but only to ensure that
                        // the v.clients[clientIndex] will not lead to index out of range
    && v.server == true
    // && (forall x:bool | x in v.clients :: x == false) // we are not using inductive invariants for safety properties here
                                // so we may need to check the states to be safe beforehand 
    && v.clients[clientIndex] == false
    && v'.server == false
    && v'.clients == v.clients[clientIndex := true]
}

ghost predicate Release(c:Constants, v:Variables, v':Variables, clientIndex:nat){
    && ValidSetup(c, v, v', clientIndex)
    && v.server == false
    && v.clients[clientIndex] == true
    && v'.server == true
    && v'.clients == v.clients[clientIndex := false]
}
/*}*/
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
/*{*/
  | Acquire(clientIndex:nat)
  | Release(clientIndex:nat)
/*}*/

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
/*{*/
  case Acquire(clientIndex) => Acquire(c,v,v',clientIndex)
  case Release(clientIndex) => Release(c,v,v',clientIndex)
/*}*/
}

ghost predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(c:Constants, v:Variables) {
/*{*/
  forall i:nat, j:nat|
    && v.WellFormed(c)
    && 0 <= i < c.numClients
    && 0 <= j < c.numClients
    && v.clients[i] == true 
    && v.clients[j] == true
      :: i == j
/*}*/
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(c: Constants, v: Variables, clientIndex: nat)
  requires v.WellFormed(c)
{
/*{*/
  && c.ValidIndex(clientIndex)
  && v.clients[clientIndex] == true
/*}*/
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (c: Constants, behavior:seq<Variables>)
    requires clientA == 2
    requires clientB == 0
    ensures 0 < |behavior|  // precondition for index operators below
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1]) // Behavior satisfies your state machine
    ensures forall i | 0 <= i < |behavior| :: Safety(c, behavior[i]) // Behavior always satisfies the Safety predicate
    ensures behavior[0].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[0], clientA)
    ensures behavior[|behavior|-1].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[|behavior|-1], clientB)
{
/*{*/
    behavior := [Variables(false, [false, false, true]), Variables(true, [false, false, false]), Variables(false, [true, false, false])];
    c := Constants(3);

    assert Release(c, behavior[0], behavior[1], clientA);
    var step := Step.Release(clientA);
    assert(NextStep(c, behavior[0], behavior[1], step));

    assert Acquire(c, behavior[1], behavior[2], clientB);
    step := Step.Acquire(clientB);
    assert NextStep(c, behavior[1], behavior[2], step);  
/*}*/
}
