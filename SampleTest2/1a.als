abstract sig A, B{}
one sig A1, A2, A3 extends A {}
one sig B1, B2 extends B {}

one sig R { r : A some -> lone B }{ r[A1] = r[A2] && r[A1] = B1}

run {} for 4
