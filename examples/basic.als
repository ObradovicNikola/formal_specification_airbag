// Signatures:
sig A{}

// Predicates and facts
fact {
//	#A > 2
}

pred atLeastOne {
	#A > 0
}

pred anotherPred {
	#A != 1
}

pred finalPred {
	atLeastOne && anotherPred
}

// Assertions

// Commands
run finalPred
