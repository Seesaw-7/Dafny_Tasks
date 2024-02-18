datatype Variables = Variables(tokens:nat)

predicate Init(v:Variables) {
  v.tokens > 0
}

predicate Play(v:Variables, v':Variables, take:nat) {
  && 1 <= take <= 4
  && v'.tokens == v.tokens - take
}

ghost predicate Next(v:Variables, v':Variables) {
  exists take :: Play(v, v', take)
}

//Note: No safety rule gurantees that v.tokens will always be greater than 0
//Note: predicate Next ought to be ghost, else non-compilable
//Actually all state predicates should be ghost, cuz they do not perform real transitions