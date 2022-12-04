abstract sig Stanowisko {kto: Osoba, mniej: set Stanowisko}
one sig Kasjer extends Stanowisko {}
one sig Menadzer extends Stanowisko {}
one sig Straznik extends Stanowisko {}

abstract sig Osoba {zajmuje: Stanowisko, jedynak: Jedynak}
one sig Brown extends Osoba {}
one sig Jones extends Osoba {}
one sig Smith extends Osoba {}

abstract sig Jedynak {}
one sig T extends Jedynak {}
one sig N extends Jedynak {}

//fact {all s: Stanowisko | s.kto.zajmuje = s}
//fact {all o: Osoba | o.zajmuje.kto = o}
fact {kto = ~zajmuje}

fact {Brown.jedynak = N}
fact {Straznik.kto.jedynak = T}

//fact {Straznik.mniej in Kasjer+Menadzer} //za slabe ograniczenie
fact {#Straznik.mniej = 2}
fact {no s: Stanowisko | s in s.mniej}
fact {Menadzer.mniej in Smith.zajmuje}
//fact {all disj s1, s2: Stanowisko | #s1.mniej = 0 => #s2.mniej > 0}

fact {some Menadzer.mniej and Menadzer.mniej in Smith.zajmuje}

fact {no s1, s2: Stanowisko | s1 in s2.mniej and s2 in s1.mniej}

assert ktojestkim
{
	Straznik.kto = Jones
	Menadzer.kto = Brown
	Kasjer.kto = Smith
}

check ktojestkim
