module FileSystem

//Because we want the "Object" set to only contain elements in its 2 subsets and no other types/objs we use the abstract kw
abstract sig Object {}

//File and Dir are subsets of the encompassing, Object set
/*
sig File in Object {}
sig Dir in Object {}

*/
/*
Predicates that are always checked w/out the need to run them, so facts...
Since an Object can't be both a File and a Dir the expression bellow is used.
Notes:
 the operand "no" evaluates to a boolean expression if the set it's evaluating is empty
 the operand "&" is for set intersection
Conclusion: "no File & Dir" is the same as saying the intersection bw/ the 2 sets should be the empty set
*/

/*
Since the "in" operand doesn't explicitly mean the sets are non overlaping the fact bellow is needed to force it
fact { no File & Dir }
However we can define the sigs w/ a different kw to make the subsets disjoint
*/

sig File extends Object {}
sig Dir extends Object {
  entries : set Entry
  //Binary Relation where maps a Dir to a set of Entries
}

/*
a "check" command verifies that, up to the specified scope, the formula declared between brackets is implied
by the declared facts. If that is not the case we will get a counter-example instance, one where the facts hold
but the formula to be checked doesn’t.


Trying to run this, Alloy gives off a warning saying this check is irrelevant/redundant
check { no File & Dir }
this check could also be done using the "none" constant which is empty set
check { none = File & Dir }

*/


//Signatures can use multipliers to force the creation of specific sets. Say we wanted a Root dir:
one sig Root extends Dir {}
/*
Multipliers:
one -> exactly one
some -> no less than one
lone -> 0 or 1
*/

/*
Enumeration signatures

In Alloy it is very common to use extension signatures of multiplicity one in the declaration of signatures that behave like enumerated data types.
For example, the following specification declares a Color signature that contains exactly three colors: Red, Green, and Blue.

abstract sig Color {}
one sig Red, Green, Blue extends Color {}

Here we see another feature of the Alloy language: if two or more signatures share the same features 
(multiplicity, parent signature, etc) they can all be defined together in the same declaration.

This pattern for declaring signatures that essentially correspond to enumerated data types is so common, that Alloy has a keyword "enum"
for that purpose. Using this keyword, the Color signature could be declared as follows:
enum Color { Red, Green, Blue }
*/

/*
In our specification we will need two more signatures: one to model the entries in a directory,
and another to represent the possible names of directories and files. Why not just use Strings for Name? String is a predef type in Alloy and
comes with additional logic that is unecessarry in most cases and just makes it harder to work with.
*/
sig Entry {
 	name : one Name,
	content : one Object
}
sig Name {}

pred show {
	some File
	some Dir-Root //some Dirs other than Root
}

/*
Suppose: 
e : Entry is a singleton set containing an entry
d : Dir a singleton set containing a directory.
( . ): Composition Operand of Relational Logic

Accessing set fields like class params in OOP:
	e.name: denotes the name of e
	d.entries: retrieves the set of all entries in directory d

Accessing sig fields, like if you had a set of all the instances of a class in OOP:
	Entry.name: is the set of all names of all entries 
	Dir.entries: is the set of all entries that belong to some directory

Backwards Navigation/Composition:
	entries.e: denotes the set of directories that contain entry e
	entries.Entry: is the set of all directories that contain some entry.

Chaining Composition:
	d.entries.content: denotes the set of all file system objects that are contained in the entries of directory d
	entries.content.d: denotes the set of all directories with entries that contain directory d
*/
/*
fact {
	 // Entries cannot be shared between directories
 	//all x,y : Dir | x != y implies no (x.entries & y.entries)
	 all disj x,y : Dir | no (x.entries & y.entries)
	// disj is disjoint, meaning x != y
}
*/
fact {
	// Entries cannot be shared between directories, same as above
  	all e : Entry | lone entries.e
}

/*
Alloy has a special formula syntax to directly restrict the multiplicities of both end points of a binary relation. 
For example, to state that a relation r relates every atom of source signature A to at most one atom of target
signature B, and every atom of B to at least one atom of A, we could write the formula:
	r in A some -> lone B
Not stating a multiplicity next to an end point is the same as having multiplicity set. 
With this special syntax, we could have yet another alternative formulation of our first constraint.

fact {
  // Entries cannot be shared between directories
  entries in Dir lone -> Entry
}
*/
fact {
  // Different entries in the same directory must have different names
  all d : Dir, n : Name | lone (d.entries & name.n)
}
/*fact {
  // Different entries in the same directory must have different names
  all d : Dir, disj x, y : d.entries | x.name != y.name
}*/

fact {
   // Directories cannot contain themselves
   all d : Dir | d not in d.entries.content
}

fact {
  // Entries must belong to exactly one a directory
  entries in Dir one -> Entry
}

fact {
  // Every object except the root is contained somewhere
  Entry.content = Object - Root
}

fact {
  // Content is injective
  content in Entry lone -> Object
}

/*
Transitive Closure

Root.entries.content +
Root.entries.content.entries.content +
Root.entries.content.entries.content.entries.content +
... How to access all the content of all the entries if the entries themselves can be content?
(^) 
*/

//run show for 4

assert no_partitions {
  // Every object is reachable from the root
  Object-Root = Root.^(entries.content)
}

fact {
   // Directories cannot contain themselves directly or indirectly
   all d : Dir | d not in d.^(entries.content)
}

check no_partitions

