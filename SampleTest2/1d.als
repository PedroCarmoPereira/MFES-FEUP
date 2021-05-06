abstract sig A, B {}
one sig A1, A2, A3 extends A {}
one sig B1, B2 extends B {}
one sig R { r : A  lone -> some B }{}

run {} for 4
