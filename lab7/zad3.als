abstract sig Stanowisko {kto: Osoba}
one sig Ekspedient extends Stanowisko {}
one sig Kasjer extends Stanowisko {}
one sig Biurowy extends Stanowisko {}
one sig Administrator extends Stanowisko {}
one sig Kierownik extends Stanowisko {}

abstract sig Osoba
{
	zajmuje: Stanowisko,
	lunch: Lunch,
	plec: Plec,
	siostry: set Osoba
}
one sig Allen extends Osoba {}
one sig Bennett extends Osoba {}
one sig Clark extends Osoba {}
one sig Davis extends Osoba {}
one sig Ewing extends Osoba {}

abstract sig Lunch {}
one sig Wczesnie extends Lunch {}
one sig Pozno extends Lunch {}

abstract sig Plec {}
one sig K extends Plec {}
one sig M extends Plec {}

fact {zajmuje = ~kto}
fact {all o: Osoba | #o.siostry = 0 or #o.siostry = 1}
fact {no o: Osoba | M in o.siostry.plec}
fact {no o: Osoba | o in o.siostry}
fact {all o1, o2: Osoba | o1 in o2.siostry => o2 in o1.siostry}
fact
{
	Kasjer.kto.lunch = Wczesnie
	Administrator.kto.lunch = Wczesnie
	Ekspedient.kto.lunch = Pozno
	Biurowy.kto.lunch = Pozno
	Kierownik.kto.lunch = Pozno
	Allen.plec = K
	Clark.plec = K
	Allen.siostry = Clark
	Clark.siostry = Allen
	Allen.lunch = Bennett.lunch
	Kasjer.kto.plec = M
	Biurowy.kto.plec = M
	Davis.lunch = Pozno
	Ewing.lunch = Wczesnie
	Davis.plec = M
	Ewing.plec = M
	Kierownik.kto.plec = M

	Kierownik.kto not in (Davis + Ewing)
	Biurowy.kto not in Kasjer.kto.siostry
	Kasjer.kto not in Biurowy.kto.siostry

	all st: Stanowisko | one o: Osoba | st.kto = o
	all disj x, y: Stanowisko | x.kto != y.kto
	all o: Osoba | one p: Plec | o.plec = p
}

assert ktojestkim
{
	Ekspedient.kto = Allen
	Administrator.kto = Clark
	Biurowy.kto = Davis
	Kierownik.kto = Bennett
	Kasjer.kto = Ewing
}

check ktojestkim
