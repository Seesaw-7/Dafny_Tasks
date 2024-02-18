//#title Dining Philosophers
//#desc A more challenging state machine: define the state datatype.

// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table with N chairs.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).
//
// (Nota bene: The dining philosophers problem is used to illustrate deadlocks
// and deadlock-freedom. We're not doing any of that here, just using the
// example to teach you to set up a state machine model.)

datatype Constants = Constants(tableSize:nat)
{
  // An initial predicate to define well-formed constants.
  ghost predicate WellFormed() {
      && 0 < tableSize
  }
}

/*{*/
/*}*/
// Define all the relevant state in this datatype.
/*{*/
datatype Variables = Variables(chopsticks: seq<bool>)
{
  ghost predicate WellFormed(c: Constants) {
    && c.WellFormed()
    && |chopsticks| == c.tableSize
  }
}
/*}*/

ghost predicate Init(c:Constants, v:Variables) {
/*{*/
  && v.WellFormed(c)
  && forall x:bool | x in v.chopsticks :: x == false
/*}*/
}

/*{*/
ghost predicate ValidSetup(c:Constants, v:Variables, v':Variables, philosopherIndex:nat){
  && v.WellFormed(c)
  && v'.WellFormed(c)
  && philosopherIndex < c.tableSize
}

ghost function NextIdx(c:Constants, philosopherIndex:nat) : nat {
  if philosopherIndex == c.tableSize - 1 then 0 else philosopherIndex + 1
}
/*}*/

// Philosopher with index philosopherIndex acquires left chopstick
ghost predicate AcquireLeft(c:Constants, v:Variables, v':Variables, philosopherIndex:nat) {
/*{*/
  && ValidSetup(c, v, v', philosopherIndex)
  && v.chopsticks[philosopherIndex] == false
  && v' == v.(chopsticks := v.chopsticks[philosopherIndex := true])
/*}*/
}

// Philosopher with index philosopherIndex acquires right chopstick
ghost predicate AcquireRight(c:Constants, v:Variables, v':Variables, philosopherIndex:nat) {
/*{*/
  && ValidSetup(c, v, v', philosopherIndex)
  && v.chopsticks[NextIdx(c, philosopherIndex)] == false
  && v' == v.(chopsticks := v.chopsticks[NextIdx(c, philosopherIndex) := true])
/*}*/
}

// Philosopher with index philosopherIndex releases both chopsticks
ghost predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, philosopherIndex:nat) {
/*{*/
  && ValidSetup(c, v, v', philosopherIndex)
  && v.chopsticks[philosopherIndex] == true
  && v.chopsticks[NextIdx(c, philosopherIndex)] == true
  && (forall i:nat |  0 <= i < c.tableSize
        :: if || i == philosopherIndex || i == NextIdx(c, philosopherIndex) 
            then v'.chopsticks[i] == false
           else v'.chopsticks[i] == v.chopsticks[i])
  && v' == v.(chopsticks := v'.chopsticks)
/*}*/
}

datatype Step =
/*{*/
  | AcquireLeft(philosopherIndex:nat)
  | AcquireRight(philosopherIndex:nat)
  | ReleaseBoth(philosopherIndex:nat)
/*}*/

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
/*{*/
    case AcquireLeft(philosopherIndex:nat) => AcquireLeft(c, v, v', philosopherIndex)
    case AcquireRight(philosopherIndex:nat) => AcquireRight(c, v, v', philosopherIndex)
    case ReleaseBoth(philosopherIndex:nat) => ReleaseBoth(c, v, v', philosopherIndex)
/*}*/
}

ghost predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

// This predicate should be true if and only if no philosopher holds a
// chopstick.
// Since you defined the Variables state, you must define this predicate in
// those terms. Avoid using existential quantifiers.
ghost predicate NoSticksAcquired(c:Constants, v: Variables)
  requires v.WellFormed(c)
{
/*{*/
  forall x:bool | x in v.chopsticks :: x == false
/*}*/
}

// Change this predicate to be true if and only if philosopher
// `philosopherIndex` holds both of their chopsticks.
// Since you defined the Variables state, you must define this predicate in
// those terms. Avoid using existential quantifiers.
ghost predicate BothSticksAcquired(c:Constants, v: Variables, philosopherIndex: nat)
  requires philosopherIndex < c.tableSize
  requires v.WellFormed(c)
{
/*{*/
  && v.WellFormed(c)
  && v.chopsticks[philosopherIndex] == true
  && v.chopsticks[NextIdx(c, philosopherIndex)] == true
/*}*/
}

// Show that, in the Init state, no philosopher has chopsticks.
lemma InitProperty(c:Constants, v: Variables, philosopherIndex:nat)
  requires Init(c, v)
  ensures NoSticksAcquired(c, v)
{
  /*{*/
  /*}*/
}


// Show a behavior that evolves from the init state to one where a philosopher
// has completed acquiring both chopsticks.
lemma PseudoLiveness(c:Constants, philosopherIndex:nat) returns (behavior:seq<Variables>)
    requires c.tableSize == 3
    requires philosopherIndex == 1
    ensures 0 < |behavior|  // precondition for index operators below
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1]) // Behavior satisfies your state machine
    ensures behavior[0].WellFormed(c) // precondition for calling NoSticksAcquired
    ensures Init(c, behavior[0])
    ensures behavior[|behavior|-1].WellFormed(c) // precondition for calling BothSticksAcquired
    ensures BothSticksAcquired(c, behavior[|behavior|-1], philosopherIndex)  // Behavior ultimately achieves acquisition for philosopherIndex
{
/*{*/
    behavior := [Variables([false, false, false]), Variables([false, true, false]), Variables([false, true, true])];

    assert AcquireLeft(c, behavior[0], behavior[1], philosopherIndex);
    var step := Step.AcquireLeft(philosopherIndex);
    assert(NextStep(c, behavior[0], behavior[1], step));

    assert AcquireRight(c, behavior[1], behavior[2], philosopherIndex);
    step := Step.AcquireRight(philosopherIndex);
    assert NextStep(c, behavior[1], behavior[2], step);
/*}*/
}