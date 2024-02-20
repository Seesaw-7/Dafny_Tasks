datatype Card = Shelf | Patron(name: string)
datatype Book = Book(title: string)
type Variables = map<Book, Card>

ghost predicate Init(v: Variables) {
  forall book | book in v :: v[book] == Shelf
}

ghost predicate CheckOut(v : Variables, v' : Variables, book: Book, name: string) {
  && book in v
  && v[book] == Shelf
  && (forall book | book in v :: v[book] != Patron(name))
  && v' == v[book := Patron(name)]
}

ghost predicate CheckIn(v : Variables, v' : Variables, book: Book, name: string) {
  && book in v
  && v[book] == Patron(name)
  && v' == v[book:= Shelf]
}

datatype Step =
  | CheckOutStep(book:Book, patron:string)
  | CheckInStep(book:Book, patron:string)

ghost predicate NextStep(v:Variables, v':Variables, step:Step) {
  match step
  case CheckOutStep(book, patron) => CheckOut(v, v', book, patron)
  case CheckInStep(book, patron) => CheckIn(v, v', book, patron)
}

ghost predicate Next(v:Variables, v':Variables){
  exists step:Step :: NextStep(v, v', step)
}

ghost predicate Safety(v:Variables) {
  forall book1, book2 |
    && book1 in v
    && book2 in v
    && !v[book1].Shelf?
    && !v[book2].Shelf?
    && v[book1] == v[book2]
    :: book1 == book2
}

lemma SafetyProof()
  ensures forall v :: Init(v) ==> Safety(v)
  ensures forall v, v' :: Safety(v) && Next(v, v') ==> Safety(v') {
}
