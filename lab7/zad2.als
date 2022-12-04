abstract sig Stanowisko {kto: Osoba}
one sig Zaopatrzeniowiec extends Stanowisko {}
one sig Kasjer extends Stanowisko {}
one sig Ekspedient extends Stanowisko {}
one sig Pietrowy extends Stanowisko {}
one sig Menadzer extends Stanowisko {}

abstract sig Osoba {zajmuje: Stanowisko, plec: Plec, stan: Stan}
one sig Ames extends Osoba {}
one sig Brown extends Osoba {}
one sig Conroy extends Osoba {}
one sig Davis extends Osoba {}
one sig Evans extends Osoba {}

abstract sig Plec {}
one sig K extends Plec {}
one sig M extends Plec {}

abstract sig Stan {}
one sig Sam extends Stan {}
one sig NieSam extends Stan {}

fact {zajmuje = ~kto}
fact
{
	Ames.plec = K
	Brown.plec = K
	Conroy.plec = M
	Davis.plec = M
	Evans.plec = M
	Kasjer.kto.plec = Menadzer.kto.plec
	Zaopatrzeniowiec.kto.plec = M
	Zaopatrzeniowiec.kto.stan = Sam
	Conroy.stan = NieSam
	Menadzer.kto != Conroy
	Kasjer.kto.plec != Ekspedient.kto.plec
	Davis not in (Kasjer+Ekspedient).kto
	(Kasjer + Ekspedient).kto.stan = Sam
	(Evans + Ames) != (Kasjer + Ekspedient).kto
}

assert ktojestkim
{
	Ekspedient.kto = Evans
	Kasjer.kto = Brown
	Menadzer.kto = Ames
	Pietrowy.kto = Conroy
	Zaopatrzeniowiec.kto = Davis
}

check ktojestkim
