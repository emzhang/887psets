SPOILER ALERT!  Hints spaced thoughtfully throughout this file. ;)


Transitivity of subtyping: It's helpful to prove a different lemma with a stronger induction hypothesis.  In particular, given a single subtyping fact [t1 $<: t2], conclude a conjunction ([/\], "and") of two quantified facts based on [t1] and [t2], one for "each side of" the subtyping relation.

Canonical forms: In our original type-safety proof, it's pretty obvious that, for instance, any value of a function type is an [Abs] expression.  It's not so obvious when we add subtyping.  You'll want to use induction to prove lemmas explaining which form of values is allowed for each sort of type.


Typing inversion: There's another easy step from the original type-safety proof that becomes more of a chore with subtyping: given a typing fact with a known-shape expression, conclude something about the possible shapes of the type.  For instance, if an [Abs] has a type, it must be a function type, with respect to which the body of the [Abs] must be properly typed.  You will want to use induction to prove explicit lemmas of that form, for various expression shapes that come up.


Getting those inversion lemma statements right: In some cases, you will need to use the subtype relation to state the right conclusion of a lemma.  Most of the lemma conclusions should also begin with existential quantifiers, surrounding conjunctions.
