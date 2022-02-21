open util/ordering[Time] as T

sig Time {}

sig Speed {
	value: Int
}

fact speed_val {
	all s: Speed | s.value >= 0
}

-- ziroskop, sa vrednosti koju izmeri (promena gravitacione sile)
sig Gyroscope {
	g_meter: Int
}

-- ogranicenje vrednosti za g_meter
fact gyro_val {
	all g: Gyroscope | g.g_meter >= 0 and g.g_meter <= 30
}

-- TODO: definisati kocnicu i ogranicenje da uvek vazi da jacina pritiska mora da bude izmedju 0 i 1 
-- (odnosno, predstaviti kao 0 -100)
-- nakon toga, dodati kocnicu na sva mesta gde je potrebno
sig Break {
	value: Int
}

fact break_val{
	all b:Break | b.value >= 0 and b.value <= 100
}

abstract sig Sensor {
}

sig ImpactSensor, SideSensor, SeatWeightSensor, SeatbeltSensor extends Sensor {}

abstract sig Switch {
	on: set Time
}

abstract sig AirbagPosition {}
sig Normal, Knee extends AirbagPosition {}

sig AirbagSwitch extends Switch {}

sig ACUSensors {
	speed: Speed one -> Time,
	break: Break one -> Time,
	gyro: Gyroscope one -> Time,
	frontal: ImpactSensor one -> Time,
	side: SideSensor one -> Time
}

some sig Airbag {
	on: set Time,
	activated: set Time, 
	seatbelt: SeatbeltSensor one -> Time,
	weight: SeatWeightSensor one -> Time,
	switch: AirbagSwitch one -> Time, 
	sensors: ACUSensors one -> Time,
	position: AirbagPosition
}

-- samo "ukljucivanje" u smislu da je airbag u stanju pripravnosti
-- aktivacija se naknadno može desiti jedino ukoliko je airbag "ukljucen"
pred turn_on [a: Airbag, t, t': Time ] { 
	-- precondition: airbag is off
	!is_on[a, t]
	-- postcondition: airbag is on
	is_on[a, t']
}

-- TODO: iskljucivanje
-- dodati ga i kasnije gde je potrebno
pred turn_off[a: Airbag, t, t':Time] {
	-- precondition: airbag is on
	is_on[a,t]
	-- postcondition: airbag is off
	!is_on[a,t']
}


-- aktivacija jednog airbag-a
pred activate[a: Airbag, t, t': Time] {
	-- preconditions
	is_on[a, t]
	are_conditions_ok[a, t]
	!is_activated[a, t]

	-- postcondition
	is_activated[a, t']
	-- frame condition
	activated_changes[Airbag - a, t, t']
}

pred still_impact [a: Airbag, t, t': Time] {
	-- precondition
	(let s = a.sensors.t | 
	let speed = s.speed.t |
		speed.value < 3)
	and
	(let s = a.sensors.t | 
	some s.frontal :> t or some s.side :> t)
	and
	(let s = a.sensors.t | 
	let gyro = s.gyro.t |
		gyro.g_meter >= 2)

	-- postcondition
	activate[a, t, t']
}

--DODATO: noga jako pritisnuta na kocnici u mirovanju
-- moze se desiti ukoliko auto miruje pod nagibom, ili u nekom drugom slucaju
pred still_impact_knee [a: Airbag, t, t': Time] {
	-- precondition
	(let s = a.sensors.t | 
	let speed = s.speed.t |
		speed.value < 3)
	and
	(let s = a.sensors.t | 
	some s.frontal :> t or some s.side :> t)
	and
	(let s = a.sensors.t | 
	let gyro = s.gyro.t |
		gyro.g_meter >= 2)
	and 	
	(let s = a.sensors.t |
	let break = s.break.t |
		break.value < 70)

	-- postcondition
	activate[a, t, t']
}

-- TODO: udarac u slucaju vece brzine
pred speed_impact [a: Airbag, t, t': Time] {
	-- precondition
--	a.position = Normal and
	(let s = a.sensors.t | 
	let speed = s.speed.t |
		speed.value >= 3) 
	and 
	(let s = a.sensors.t | 
	some s.frontal :> t or some s.side :> t)
	and
	(let s = a.sensors.t | 
	let gyro = s.gyro.t |
		gyro.g_meter > 3)
			
	-- postcondition
	activate[a, t, t']
}

-- TODO: ne zaboraviti i proveru da noga nije jako pritisnuta na kocnici
pred speed_impact_knee [a: Airbag, t, t': Time] {
	-- precondition
	(let s = a.sensors.t | 
	let speed = s.speed.t |
		speed.value >= 3) 
	and 
	(let s = a.sensors.t | 
	some s.frontal :> t or some s.side :> t)
	and
	(let s = a.sensors.t | 
	let gyro = s.gyro.t |
		gyro.g_meter > 3)
	 and 	
	(let s = a.sensors.t |
	let break = s.break.t |
		break.value < 70)

	-- postcondition
	activate[a, t, t']
}


pred is_on [a: Airbag, t: Time] {
	t in a.on and one a.switch :> t
}

pred is_activated[a: Airbag, t: Time] {
	t in a.activated
}

pred are_conditions_ok[a: Airbag, t:Time] {
	one a.switch :> t and one a.seatbelt :> t and one a.weight :> t
}

pred type_check[a: Airbag, t: Time] {
	(a.position = Normal) or
	(a.position = Knee and (let s = a.sensors.t | let break = s.break.t | break.value < 70))
}

pred activated_changes[A: set Airbag, t,t': Time] {
	all a: A |
		-- TODO: ukljuciti uslove sa senzora tezine, o vezanom pojasu i korisnickom prekidacu
		t' in a.activated iff ((is_on[a, t]) and
			(are_conditions_ok[a, t]) and
			-- kada se airbagovi lancano pozivaju, svaki mora da proveri svoj tip za slucaj aktivacije
			type_check[a, t])
}

-- TODO: predikat "transitions"
// off, on, sudari
pred transitions[t,t': Time] {
	some a: Airbag |
		turn_on[a, t, t'] or
		turn_off[a, t, t'] or
		(still_impact[a, t, t'] iff a.position = Normal) or
		(still_impact_knee[a, t, t'] iff a.position = Knee) or
		(speed_impact[a, t, t'] iff a.position = Normal) or
		(speed_impact_knee[a, t, t'] iff a.position = Knee)
}

-- airbag 1: normal

one sig A1 extends Airbag {}
one sig TNOR extends Normal {}
one sig ABS1 extends AirbagSwitch {}
one sig SWS1 extends SeatWeightSensor {}
one sig SBS1 extends SeatbeltSensor {}

-- TODO: dodati airbag za kolena i potrebne komponente
-- airbag 2: knee

one sig A2 extends Airbag {}
one sig TKNEE extends Knee {}
one sig ABS2 extends AirbagSwitch {}
one sig SWS2 extends SeatWeightSensor {}
one sig SBS2 extends SeatbeltSensor {}

-- ACU

one sig ACU1 extends ACUSensors{}
one sig G1 extends Gyroscope {}
one sig IS1 extends ImpactSensor {}
one sig DS1 extends SideSensor {}

one sig S1 extends Speed {}
one sig B1 extends Break {}

fact {
	G1.g_meter = 0
}

pred init [t: Time] {
	-- TODO: dopuniti init podacima za airbag za kolena
	A1.position = TNOR
	A1.sensors.t = ACU1
	A1.weight.t = SWS1
	A1.seatbelt.t = SBS1
	A1.switch.t = ABS1

	-- airbag za kolena
	A2.position = TKNEE
	A2.sensors.t = ACU1
	A2.weight.t = SWS2
	A2.seatbelt.t = SBS2
	A2.switch.t = ABS2

	ACU1.speed.t = S1
	ACU1.break.t = B1
	ACU1.gyro.t = G1
	ACU1.frontal.t = IS1
	ACU1.side.t = DS1	

// 	!is_on[A1, t] and !is_activated[A1, t]
 	
	-- TODO: dopuniti uslovom da i za sve ostale airbag-ove u pocetku vazi da su iskljuceni
//	!is_on[A2, t] and !is_activated[A2, t]
	all a: Airbag | !is_on[a, t] and !is_activated[a, t]
}

pred safety_check {
 some Airbag
 init [T/first]
some t: Time | safe [t]
all t: Time - T/last | 
    transitions [t, T/next[t]]
} 

pred safe [t: Time] {
  ACU1.gyro.t != G1
}

run safety_check for 4 but 8 Int, 1 Break, 1 Speed, 1 ACUSensors, 2 Airbag
//run safety_check for 4 but 8 Int, 1 Break
//run safety_check for 4 but 8 Int, 1 ACUSensors
