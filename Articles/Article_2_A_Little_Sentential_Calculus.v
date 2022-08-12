(** * Article 2: A Little Sentential Calculus *)

Module Article_2_A_Little_Sentential_Calculus.

(** printing -> %->% #-># *)
(** If you take an undergraduate course in
formal mathematical logic, you might start
with analogies to the real world.
It's an effective teaching strategy.
Formal logic has a lot of rules and
a few symbols to learn, and the student
might feel anxious about them.
But if the student can make a connection
between the familiar and the unfamiliar,
then ... well ... there should be less anxiety.

Analogies have their limits, of course,
and some analogies are so self-evidently contrived.
I have to admit that I am about to pose
a contrived example.

Let us suppose that there is an entrepreneur
named Patricia, who makes the most wonderful
marmalade out of quinces.
Patricia always buys her quinces from one
grocer, her childhood friend Robert.
Robert currently runs one store in the fabled
city of Sarnia, Ontario, and Patricia has to
go to Robert's store to buy her quinces.
(This would be in the days before DoorDash,
and I should remind you that other
food-delivery services are available.)
The question is, if Patricia is about to make
her new batch of quince marmalade,
has she been in Sarnia?

Let's work this out first:
Patricia is ready to make quince marmalade.
If Patricia is ready to make quince marmalade,
then it follows that she must have bought quinces.
If she bought quinces, and she always buys them from
Robert, then she must have been in Robert's store.
If she was in Robert's store, then she must have
been in Sarnia.

Now, we can write this formally in what is known
as the Sentential Calculus.  (Keep in mind, this
is only a little Sentential Calculus.)
We do this by assigning letters to sentences
that can be either true or false.

Like Article 1, this article is written as
a script in the vernacular of #Coq&#185;,#
and the text
that you are reading is actually written
as comments delimited by #&#40;&#42;&#42;#
and #&#42;&#41;# in the script.
(The coqdoc tool normally does not include
the #&#40;&#42;&#42;# and #&#42;&#41;#
delimiters, and I have used a trick so
that you can see them here.)

There will also be comments that are
delimited by #&#40;&#42;# and #&#42;&#41;;#
these comments are what Coq script writers
would normally include in a script.
(The coqdoc tool will include the
#&#40;&#42;# and #&#42;&#41;# delimiters.)

In this case, we have four statements:

*)

(* P stands for "Patricia is prepared to make quince marmalade." *)

Axiom P : Prop.

(* Q stands for "Patricia has bought quinces." *)

Axiom Q : Prop.

(* R stands for "Patricia was in Robert's store." *)

Axiom R : Prop.

(* S stands for "Patricia was in Sarnia." *)

Axiom S : Prop.

(**

Note that these sentences are not necessarily True.
They could be True, but they could be False as well.

Each sentence is represented by a single letter,
and each letter is declared to be a [Prop]
(this word is short for #<em>proposition</em>#).
In Coq, a proposition is considered to either
be provable or not provable.

It is now obvious how contrived this example is;
I needed something for which the letters P, Q, R, and S
could stand, and I settled on Patricia, quinces, Robert,
and Sarnia. I'll come back to that later.

The Axiom command means that Coq should assume
something without proof.
In this case, Coq should assume that
P, Q, R, and S are propositions.

To repeat the point about the sentences,
Coq is not instructed to assume that P
is True; it is only to assume that P is
a proposition (which we are associating
with the sentence
"Patricia is prepared to make quince marmalade").
Similarly, Coq is instructed to assume
that Q, R, and S are propositions,
but not to assume that they are True.

We now tell Coq to assume that P is true:

**)

(* Pr1 means it is true that "Patricia is
prepared to make quince marmalade." *)

Axiom Pr1 : P.

(**

This axiom is called a "premise",
and I have chosen to begin the name of a
premise with the prefix "Pr".
This premise states that Coq should
assume, because of Pr1, that P is True
(or more correctly, P is provably True).
Based on his #tutorial,&#178;#
Michael Nahas would refer to Pr1 as
a proof of P.

Basically, a formal proof of a
proposition in Coq is constructed
by listing proofs of other propositions
(these proofs of other propositions
are the premises) and then using tactics
to demonstrate how the premises lead
to the proposition we want to prove.
In our case, the goal is to get a
proof of S.
We cannot get this proof with only
the one premise, which is a proof of P.
We need more premises.

We got the first premise from the
statement "Patricia is ready to make
quince marmalade."  As you recall,
we had four statements; we therefore
need four premises, one for each statement.

So now, let us make a premise for the
second statement:

**)

(* Pr2 means that "if Patricia is prepared to make
quince marmalade, then she must have bought quinces." *)

Axiom Pr2 : P -> Q.

(**

The arrow pointing to the right is read "implies".
Here, we are stating that "P implies Q" or
"if P is true then Q is true", or "P is true only
if Q is true".

But what it really means: if you have a proof of P,
you can apply Pr2 to that proof
and you get another proof, this time a proof of Q.
We have a proof of #P&#160;&#8212;#
that is, #Pr1&#160;&#8212;#
so we should be able to get a proof of Q.

We have converted two of the four sentences
into premises.  Now we convert the other two:

**)

(* Pr3 means that "if Patricia has bought quinces,
then she must have been in Robert's store." *)

Axiom Pr3 : Q -> R.

(* Pr4 means that "if Patricia was in Robert's store,
then she was in Sarnia." *)

Axiom Pr4 : R -> S.

(**

Having listed our propositions and premises,
we now write our theorem.
Remember that we want to prove that Patricia
was in Sarnia, which is designated by S.
So we proceed this way:

**)

Theorem T1 : S.

Proof.

    assert (MPP5 := Pr2 (Pr1) : Q).

    assert (MPP6 := Pr3 (MPP5) : R).

    assert (MPP7 := Pr4 (MPP6) : S).

    exact MPP7.

Qed.

(**

Here, unfortunately, is the complicated bit.

We have started with four premises,
numbered one through four.
The first assertion is therefore
numbered five.

Each new statement is derived from
two other statements by a method called
"Modus Ponendo Ponens" (which is a Latin phrase
that means "the method that affirms by affirming").

The assertion MPP5 affirms Q from
[ P -> Q ] (Pr2) by affirming P (Pr1).
The order is important:
The premise with the arrow is named first,
and the premise proving the left-hand
side of the arrow is named next,
and the proposition for which we want
the proof is named last.

The assertion MPP6 affirms R from
[ Q -> R ] (Pr3) by affirming Q (MPP5).
The assertion MPP6 is like MPP5,
except that the proof of the left-hand side
is not a premise.  The proof of the left-hand
side is an earlier assertion (MPP5 in particular).
This is how proofs work in Coq: you assert
proofs of some propositions from the premises,
then you assert proofs of other propositions
from proofs that you already asserted.

The assertion MPP7 affirms S from
[ R -> S ] (Pr4) by affirming R (MPP6).
Derivation MPP7 affirms S,
which was what we want,
so we use exact to tell Coq to check
that it is indeed what we want.
We then end the proof with "Qed",
which is short for another Latin phrase,
"quod erat demonstrandum".
(Mathematical logic employs a lot of Latin.
"Quod erat demonstrandum" means
"which was to be demonstrated".)
We could read the "exact MPP7. Qed."
as "MPP7 is exactly what was to be demonstrated."

Now, the above proof is reminiscent of the way that
proofs are presented in symbolic logic courses,
where you have to write down a numbered list of formulas,
and each formula must be justified as a premise,
an assumption, or as the result of applying a
rule of inference.  This proof is based
on an exercise in G. M. Hardegree's
"Symbolic Logic" #textbook.&#179;#
It's great if you're writing proofs down by hand,
because it's easier to write single letters
than whole words.
But in the computer age, where typing words is easy,
we can be more expressive in formal proofs, like so:

**)

Axiom Patricia_is_prepared_to_make_marmalade : Prop.

Axiom Patricia_has_bought_quinces : Prop.

Axiom Patricia_was_in_Robert's_store : Prop.

Axiom Patricia_was_in_Sarnia : Prop.

Axiom Patricia_is_indeed_prepared_to_make_marmalade
    : Patricia_is_prepared_to_make_marmalade.

Axiom Patricia_needs_quinces_to_make_marmalade
    : Patricia_is_prepared_to_make_marmalade
        -> Patricia_has_bought_quinces.

Axiom Patricia_always_buys_quinces_from_Robert
    : Patricia_has_bought_quinces
        -> Patricia_was_in_Robert's_store.

Axiom Robert's_store_is_in_Sarnia
    : Patricia_was_in_Robert's_store
        -> Patricia_was_in_Sarnia.

Theorem Patricia_was_indeed_in_Sarnia : Patricia_was_in_Sarnia.

Proof.

assert (She_has_indeed_bought_quinces
    := Patricia_needs_quinces_to_make_marmalade
        ( Patricia_is_indeed_prepared_to_make_marmalade )
    : Patricia_has_bought_quinces).

assert (She_was_indeed_in_Robert's_store
    := Patricia_always_buys_quinces_from_Robert
        ( She_has_indeed_bought_quinces )
    : Patricia_was_in_Robert's_store).

assert (She_was_indeed_in_Sarnia
    := Robert's_store_is_in_Sarnia
        ( She_was_indeed_in_Robert's_store )
    : Patricia_was_in_Sarnia).

exact She_was_indeed_in_Sarnia.

Qed.

(**

Theorem T1 and theorem [Patricia_was_indeed_in_Sarnia]
are the same theorem, but in different forms.
The first theorem uses abbreviations and is very terse,
and it has comments explaining everything.
The second theorem uses whole words,
and doesn't need comments, but it is very verbose,
and I've had to use some conventions.
(For example, X_was_indeed_Y means that X_was_Y is true.)

So is theorem [Patricia_was_indeed_in_Sarnia]
easier to read and follow than theorem T1?
I would say yes, but [Patricia_was_indeed_in_Sarnia]
is easier to read than T1 much like the
three of clubs ranks higher than the two of clubs.
It's only marginally better.

I would say that there is more than one art of
computer programming #(cf. Knuth&#8308;)#
and one of those arts must be that happy medium
between terse and verbose.

So that's the second article. My plan for the
third article is to strike towards the happy medium.

** References:

#&#185;# Institut national de recherche en
sciences et technologies du numérique (Inria).
"The Coq Proof Assistant."
https://coq.inria.fr/

#&#178;# Nahas, Michael.  "Mike Nahas's Coq Tutorial."
https://mdnahas.github.io/doc/nahas_tutorial.v

#&#179;# Hardegree, G. M. (1999)
    "Symbolic Logic: A First Course."
    McGraw-Hill College.
    Section 5.22, exercise 1.
    <https://courses.umass.edu/phil110-gmh/MAIN/IHome-5.htm>

Knuth, D. E. (1997, 1998, 2011)
    "The Art of Computer Programming."
    Addison-Wesley. Four volumes.

**)

End Article_2_A_Little_Sentential_Calculus.

