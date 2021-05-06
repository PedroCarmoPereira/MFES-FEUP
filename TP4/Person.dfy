datatype Sex = Masculine | Feminine
datatype CivilState = Single | Married | Divorced | Widow | Dead
 
class {:autocontracts} Person
{
    const name: string; // ‘const’ for immutable fields
    const sex: Sex;
    const mother: Person?; // ‘?’ to allow null
    const father: Person?;
    var spouse: Person?;
    var civilState: CivilState;

	ghost var ancestors: seq<Person>;
 
	predicate Valid()
	reads this
	reads spouse
	{
        (civilState == Married ==> spouse != null && spouse != null ==> civilState == Married) &&
		(mother != null ==> mother.sex == Feminine) && (father != null ==> father.sex == Masculine) &&
		(spouse != null ==> spouse.spouse == this)
	}

    constructor (name: string, sex: Sex, mother: Person?, father: Person?)
    {
        this.name := name;
        this.sex := sex;
        this.mother := mother;
        this.father := father;
        this.spouse := null;
        this.civilState := Single;
		this.ancestors := [];
		if mother != null {
			this.ancestors := this.ancestors + mother.ancestors + [mother];
		}

		if father != null {
			this.ancestors := this.ancestors + father.ancestors + [father];
		}
    }
 
    method marry(spouse: Person)
	modifies spouse
	modifies this
    {
        spouse.spouse := this;
        spouse.civilState := Married;
        this.spouse := spouse;
        this.civilState := Married;
    }
 
    method divorce()
	requires Valid() && spouse != null && spouse.civilState == Married
	modifies spouse
	modifies this
    {
        spouse.spouse := null;
        spouse.civilState := Divorced;
        this.spouse := null;
        this.civilState := Divorced;
    }
 
    method die()
	requires Valid()
	modifies this
	modifies spouse 
    {
        if spouse != null
        {
            spouse.spouse := null;
            spouse.civilState := Widow;
        }
        this.spouse := null;
        this.civilState := Dead;
    }
}
