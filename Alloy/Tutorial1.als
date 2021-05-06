//Comment

/*
multiline 
comment
*/
//In alloy we start files with the keyword module and a name;
module Tutorial/addressBook

//Tells alloy we have 2 signatures/objects/sets (sig) one called Names, and the other Addr
sig Name, Addr {}

sig Book{
	//adds relation in Book, named addr; that maps a name to 0 or 1 addresses (lone)
	addr: Name -> lone Addr
}

/*
A predicate is like a function that can me executed (pred), but only evaluates to a True or False Result
for 3 -> means create up to 3 instances of the objects max (3 Names and 3 Addr)
but 1 Book -> excludes Book from the for, meaning total objcts created will be max  (3 Names and 3 Addr and 1 Book)
*/
pred show {} 
//run show for 3 but 1 Book
/*
We can click the "Show" button to see different examples of the run to test
for predicate and model consistency and beheviour.
"Show" menu starts off in graphical mode, but can be switched on top bar.
Also on the "Show" menu/popup, we can focus on a signature, like Book ("Projection" Button), to see what's inside it.
*/

//This predicate takes an argument of the Book type
pred showV2 (b:Book){
	//Said book, must have at least 2 entries in it's addr relation, meaning it's cardinality (#) must be greater than 1
	#b.addr > 1
	//For all element in Name, there must be an addr
	#Name.(b.addr) > 1
}
//run showV2 for 3 but 1 Book

pred add(b_old, b_new:Book, n:Name, a:Addr){
	b_new.addr = b_old.addr + n->a
}

//We can add a wrapper pred for add and call it like so
pred showAdd(b_old, b_new:Book, n:Name, a:Addr){
	add[b_old, b_new, n, a]//Calls Predicate add
	#Name.(b_new.addr) > 1
}
//We can have multiple run statements uncommented :P
//run showAdd for 3 but 2 Book

//Predicate for deleting all entries in book with a certain name
pred del(b_old, b_new:Book, n:Name){
	b_new.addr = b_old.addr - n -> Addr //removes all entries of n -> Some Addr from the old book
}

pred showDel(b_old, b_new:Book, n:Name){
	del[b_old, b_new, n]
}

run showDel for 3 but 2 Book

//Functions in Alloy (fun) can return things other than T/F, in this case a set of Addr
fun lookup(b:Book, n:Name): set Addr {
	n.(b.addr) // returns set of 
}

assert delUndoesAdd {
	all b0, b1, b2:Book, n:Name, a:Addr |
		//add[b0, b1, n, a] and del[b1, b2, n] implies b0.addr = b2.addr //This was breaking in the case that b0 = {(n, a)} and then we tried to add n -> again, so the new version checks if b4 the add the rel exists
		no n.(b0.addr) and add[b0, b1, n, a] and del[b1, b2, n] implies b0.addr = b2.addr
}

assert addIdempotent {
	all b0, b1, b2:Book, n:Name, a:Addr |
		add[b0, b1, n, a] and add[b1, b2, n, a] implies b2.addr = b1.addr
}

assert addLocalDoesNotAffectOtherElems{
	all b0, b1:Book, n0, n1: Name, a:Addr | 
		add[b0, b1, n0, a] and n0 != n1 implies lookup[b0, n1] = lookup[b1, n1]
}

check  addLocalDoesNotAffectOtherElems for 10 but 3 Book














