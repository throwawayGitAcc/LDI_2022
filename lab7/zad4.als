sig Osoba {para: Osoba, usciskal: set Osoba}

one sig Agata extends Osoba {}
one sig Andrzej extends Osoba {}

fact {para = ~para}
fact {usciskal = ~usciskal}
fact {Agata.para = Andrzej}
fact {no o: Osoba | o.para = o}
fact {no o: Osoba | o in o.usciskal}
fact {no o: Osoba | o.para in o.usciskal}

fact {all disj o1, o2: Osoba |  (o1 != Agata and o2 != Agata) =>  #o1.usciskal != #o2.usciskal}

pred test {}
run test for exactly 10 Osoba
