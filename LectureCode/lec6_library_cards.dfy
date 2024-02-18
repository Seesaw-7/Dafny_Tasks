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
     //just need to check in the book, no need to care about others cuz it won’t violate safety rules ever
}

ghost predicate Next(v: Variables, v': Variables) {
  || (exists book, name :: CheckOut(v, v', book,name))
  || (exists book, name :: CheckIn(v, v',book,name))
}
