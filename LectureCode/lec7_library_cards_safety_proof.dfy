include "lec6_library_cards.dfy"

ghost predicate HasAtMostOneBook(v:Variables, name:string) {
  forall book1, book2 |
    && book1 in v
    && book2 in v
    && v[book1] == Patron(name)
    && v[book2] == Patron(name)
    :: book1 == book2
}

ghost predicate Safety(v:Variables) {
  forall name :: HasAtMostOneBook(v, name)
}

lemma SafetyProof()
  ensures forall v :: Init(v) ==> Safety(v)
  ensures forall v, v' :: Safety(v) && Next(v, v') ==> Safety(v') {
  forall v, v' | Safety(v) && Next(v, v') ensures Safety(v') {
    forall name ensures HasAtMostOneBook(v', name){
      if exists book, patron :: CheckIn(v,v',book,patron) {
        var book, patron :| CheckIn(v,v',book,patron);
        if name == patron {
          assert HasAtMostOneBook(v', name);
        } else {
          assert HasAtMostOneBook(v, name);//trigger (the fact that dafny was missing to complete the proof)
          assert HasAtMostOneBook(v', name);
        }
      } else {
        assume false;
        assert HasAtMostOneBook(v', name);
      }
    }
  }
}

// we only need to keep the 'trigger'
lemma SafetyProof2()
  ensures forall v :: Init(v) ==> Safety(v)
  ensures forall v, v' :: Safety(v) && Next(v, v') ==> Safety(v') {
  forall v, v' | Safety(v) && Next(v, v') ensures Safety(v') {
    forall name ensures HasAtMostOneBook(v', name){
      assert HasAtMostOneBook(v, name);//trigger (the fact that dafny was missing to complete the proof)
    }
  }
}
