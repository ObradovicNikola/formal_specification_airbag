// wheel: {wheel0, wheel1, wheel2}
sig wheel {} {
	this in (Bicycle.front + Bicycle.rear)
}

// Bicycle: {Bicycle0, Bicycle1, Bicycle0}
sig Bicycle {
	// one (default), lone 0-1, set 0..N
	front: wheel,
	rear: wheel
} {
	rear != front
}

//fact  {
//	all b: Bicycle | b.rear != b.front
//}

fun allWheels[b: Bicycle]: set wheel {
	b.front + b.rear
}

pred notIn[w: wheel, b: Bicycle] {
	w not in allWheels[b]
}

fact {
	all b1, b2: Bicycle |
		b1 != b2 =>
		notIn[b1.front, b2] &&
		notIn[b1.rear, b2]
}

fact {
	#Bicycle > 0
}

//fact {
//	#wheel = 8
//	#Bicycle = 3
//}

run {} for 3 but 6 wheel
