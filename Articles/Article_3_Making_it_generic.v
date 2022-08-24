(** * Article 3: Making it generic *)

Module Article_3_Making_it_generic.

(** printing -> %->% #-># *)
(** printing forall %forall% #forall# *)
(** You might remember that, in the previous
article of this series, I presented two
proofs in #Coq&#185;#
of the same situation, which was
something about quinces.  I will reproduce
the verbose version here: *)

Section Verbose_example.

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
			(Patricia_is_indeed_prepared_to_make_marmalade)
			: Patricia_has_bought_quinces).

		assert (She_was_indeed_in_Robert's_store
			:= Patricia_always_buys_quinces_from_Robert
			(She_has_indeed_bought_quinces)
			: Patricia_was_in_Robert's_store).

		assert (She_was_indeed_in_Sarnia
			:= Robert's_store_is_in_Sarnia
			(She_was_indeed_in_Robert's_store)
			: Patricia_was_in_Sarnia).

		exact She_was_indeed_in_Sarnia.

	Qed.

End Verbose_example.

(** And I will reproduce the terse example
#here:&#178;# *)

Module Terse_example.

	Axiom P : Prop.

	Axiom Q : Prop.

	Axiom R : Prop.

	Axiom S : Prop.

	Axiom Pr1 : P.

	Axiom Pr2 : P -> Q.

	Axiom Pr3 : Q -> R.

	Axiom Pr4 : R -> S.

	Theorem T1 : S.

	Proof.

		assert (MPP5 := Pr2 (Pr1) : Q).

		assert (MPP6 := Pr3 (MPP5) : R).

		assert (MPP7 := Pr4 (MPP6) : S).

		exact MPP7.

	Qed.

End Terse_example.

(** Now the terse example is easier to follow
than the verbose example.  When everything
is named by a letter or an abbreviation,
you can easily see that we can go from
P to S:  We can go from P to Q, and
then from Q to R, and then from R to S.
In more mathematical language, we would
say that P is true (because Pr1 says that
P is true), and therefore Q is true
(because Pr2 says that P implies Q),
and therefore R is true (because Pr3
says that Q implies R), and finally,
that S is true (because Pr4 says that
R implies S).

I have more words to define before I proceed.

In the command "Theorem T1 : S",
the proposition S is called the "goal".
When you enter this command, Coq does not just
blindly accept the Theorem to be true.
Instead, immediately after the Theorem command,
Coq goes into "proof-editing mode";
it effectively demands that you prove your theorem.
You cannot normally leave proof-editing mode
until you actually write the Proof of the Theorem.
This mirrors how papers, journals, and textbooks
(for the college-and-university level,
at least) are written:
A theorem is stated, and its proof
is immediately printed after the theorem.

The "assert" command is called a "tactic".
A tactic in Coq is a step towards proving the goal.
Tactics in Coq usually start with lowercase letters
instead of uppercase letters.

You can, and should, surmise that "exact" is also a tactic.

While in proof-editing mode, you must enter a tactic to proceed.
The tactic may introduce intermediate results that are known to
be true based on the current environment inside the proof
("assert" is such a tactic).  The tactic may also find the
goal within the current environment and state that the
goal has been achieved ("exact" is an example of such a tactic).
There are other tactics that add new goals and resolve other goals
in the middle of a proof.

That sounds like a lot of juggling for you and Coq to do.
It is a lot of juggling for a human to do.
Coq is a "proof assistant" in that it keeps track
of everything that you've done, and it enforces that
every tactic that you use is valid.
(However, Coq is not a "theorem prover".
You cannot just give Coq a theorem and expect it
to automatically generate the proof.
This is actually a limit of computer science itself,
not of Coq specifically.)

Now back to the examples.
The two examples are in fact similar:

  - 1.	Both of them declare, as Axioms, four Propositions.

  - 2.	Both of them declare, as a fifth Axiom,
	that the first Proposition is true.

  - 3.	Both of them declare, as a sixth Axiom,
	that the second Proposition is true
	if the first Proposition is true.

  - 4.	Both of them declare, as a seventh Axiom,
	that the third Proposition is true
	if the second Proposition is true.

  - 5.	Both of them declare, as an eighth Axiom,
	that the fourth Proposition is true
	if the third Proposition is true.

  - 6.	Finally, both of them prove that the
	fourth Proposition is true because
	of all eight Axioms.

The difference between the two examples is that
it is obvious from the terse example what the
structure of the proof is,
but we don't necessarily know what the letters mean
(unless we include the comments that we had last time);
the verbose example uses wordy phrases to name each Axiom,
making the structure of the proof harder to spot.

So how do we solve a word problem like the one we have
with Patricia, quinces, Robert, and Sarnia?
What we could do is recognize that the terse proof is
actually generic.  We could print out the terse proof,
set it beside our keyboard, assign meaningful names
to each of the letters (P stands for
Patricia_is_prepared_to_make_marmalade,
Q stands for Patricia_has_bought_quinces, and so on)
and type in our word-problem proof into Coq using the new names,
and be done with it.  Problem solved.

Or ... we might try to write the terse proof in such a way
that Coq is able to reuse it to prove the verbose theorem.

First off, we can restrict the letters P, Q, R, and S
so that they only apply to the Theorem and its proof.
Instead of declaring the letters separately as Axioms,
we put the letters in parentheses between the Theorem's name
and the ": S".
We can also put the premises in parentheses after
the Theorem name and restrict them to the Theorem as well.
(In fact, if we move the letters into parentheses,
then the premises also have to go into the parentheses
after the letters, because the letters will no longer
have meaning outside of the Theorem.)

Note that the name "MPP_three_times" means to
apply the rule "Modus ponendo ponens"
(the method, by affirming one thing,
of affirming a second thing) three times.

We do that and we get this:

**)

Module First_version_of_MPP_three_times.

	Theorem MPP_three_times
		(P : Prop) (Q : Prop)
		(R : Prop) (S : Prop)
		(Pr1 : P)
		(Pr2 : P -> Q)
		(Pr3 : Q -> R)
		(Pr4 : R -> S) : S.

	Proof.

		assert (MPP5 := Pr2 (Pr1) : Q).

		assert (MPP6 := Pr3 (MPP5) : R).

		assert (MPP7 := Pr4 (MPP6) : S).

		exact MPP7.

	Qed.

	(** Theorem MPP_three_times is generic.
  What that means is that it has eight
  parameters (four propositions and
  four axioms based on the propositions),
  and we can use MPP_three_times
  by writing MPP_three_times
  followed by eight arguments.
  For example: *)

	Theorem Patricia_was_indeed_in_Sarnia
		: Patricia_was_in_Sarnia.

	Proof.

		assert (She_was_indeed_in_Sarnia := MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

		exact She_was_indeed_in_Sarnia.

	Qed.

	(** Each of the parameters in MPP_three_times
  is replaced by an argument (P is replaced
  by Patricia_is_prepared_to_make_marmalade,
  Q is replaced by Patricia_has_bought_quinces,
  and so on).  MPP_three_times then outputs
  a proof that Patricia_was_in_Sarnia
  (which is the argument for the parameter S),
  which we call She_was_indeed_in_Sarnia.

	Note that the order of the Axioms matters
  when using the MPP_three_times Theorem.
	The following Proof shows that putting the
	Axioms in the wrong order will not work. *)

	Theorem Patricia_was_indeed_in_Sarnia_with_failures
		: Patricia_was_in_Sarnia.

	Proof.

		Fail assert (She_was_indeed_in_Sarnia := MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_was_in_Robert's_store) (* Should have been 3rd *)
			(Patricia_has_bought_quinces)    (* Should have been 2nd *)
			(Patricia_was_in_Sarnia)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)).

		Fail assert (She_was_indeed_in_Sarnia := MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_is_indeed_prepared_to_make_marmalade) (* Should have been 5th *)
			(Patricia_was_in_Sarnia)                        (* Should have been 4th *)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

		assert (She_was_indeed_in_Sarnia := MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

		exact She_was_indeed_in_Sarnia.

	Qed.

	(** The Fail prefix is useful in scripts
  for writing commands and tactics.

	Normally, a command that Coq determines to be valid
	is just executed and Coq continues,
	but a command that Coq determines to be invalid
	will cause Coq to stop and display an error message
	that you will have to make corrections.
	The same situation applies to tactics.

	The Fail prefix works in the exact opposite way:
	If Coq determines that the command prefixed by Fail
	is invalid, Coq displays a diagnostic message
	(the command has indeed failed) and continues.
	But if the command prefixed by Fail is actually valid,
	then Coq stops and displays an error message.
	The same situation applies to a tactic with
	the Fail prefix.

	The Fail prefix is useful in scripts such as
	this article.
	I don't have to tell you that
  a command will fail; I can write
  Fail followed by command
  and Coq will verify that the command
  does fail.

	There are other changes we can make.
	We don't really need to assert
  She_was_indeed_in_Sarnia separately;
	we can just put the MPP_three_times
  term directly inside the exact tactic: *)

	Theorem Patricia_was_indeed_in_Sarnia_more_direct
		: Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

	Qed.

End First_version_of_MPP_three_times.

(** Similarly, we don't really need to
    assert MPP7; we can just replace MPP7
    with the term Pr4 (MPP6)
    inside the exact tactic: **)

Module Second_version_of_MPP_three_times.

	Theorem MPP_three_times
		(P : Prop) (Q : Prop)
		(R : Prop) (S : Prop)
		(Pr1 : P)
		(Pr2 : P -> Q)
		(Pr3 : Q -> R)
		(Pr4 : R -> S) : S.

	Proof.

		assert (MPP5 := Pr2 (Pr1) : Q).

		assert (MPP6 := Pr3 (MPP5) : R).

		exact (Pr4 (MPP6)).

	Qed.

	Theorem Patricia_was_indeed_in_Sarnia_more_direct
		: Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

	Qed.

End Second_version_of_MPP_three_times.

(** At this point, let me explain the Modules
First_version_of_MPP_three_times
and Second_version_of_MPP_three_times.

Normally, once you have used a name,
you cannot use it again.  So I could
not have used the name MPP_three_times
twice: once to refer to a theorem with
a proof, and the other time to refer to
the same theorem with a slightly
different proof.

The solution to this difficulty
is to put one proof of MPP_three_times
in a Module and the other definition of
MPP_three_times in a second module.

You can compare the difference between
the two proofs of MPP_three_times in
each module: the second proof does away
with one of the assert tactics.

You can also note that the two proofs of
Patricia_was_indeed_in_Sarnia_more_direct
appear identical; the only difference is
in the proof of MPP_three_times.
Patricia_was_indeed_in_Sarnia_more_direct
depends in both cases on the Theorem
MPP_three_times but not on the Proof of
the Theorem.  This is completely normal
in computer programming, and it is known
as "abstraction".  MPP_three_times,
the name of the Theorem, is the abstraction,
and its Proof is the actual details
that the name MPP_three_times hides.

Now back to the Proof on MPP_three_times.
We don't even need to assert MPP6 either;
we can just replace MPP6 with the term Pr3 (MPP5)
inside the exact tactic:

*)

Module Third_version_of_MPP_three_times.

	Theorem MPP_three_times
		(P : Prop) (Q : Prop)
		(R : Prop) (S : Prop)
		(Pr1 : P)
		(Pr2 : P -> Q)
		(Pr3 : Q -> R)
		(Pr4 : R -> S) : S.

	Proof.

		assert (MPP5 := Pr2 (Pr1) : Q).

		exact (Pr4 (Pr3 (MPP5))).

	Qed.

	Theorem Patricia_was_indeed_in_Sarnia_more_direct
		: Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

	Qed.

End Third_version_of_MPP_three_times.

(** Again, the Theorem
Patricia_was_indeed_in_Sarnia_more_direct
and its Proof in the
Module Third_version_of_MPP_three_times
are identical to its appearance in the
first two Modules; MPP_three_times continues
to work as before.

We don't even need to separately assert
MPP5 either: *)

Module Fourth_version_of_MPP_three_times.

	Theorem MPP_three_times
		(P : Prop) (Q : Prop)
		(R : Prop) (S : Prop)
		(Pr1 : P)
		(Pr2 : P -> Q)
		(Pr3 : Q -> R)
		(Pr4 : R -> S) : S.

	Proof.

		exact (Pr4 (Pr3 (Pr2 (Pr1)))).

	Qed.

	Theorem Patricia_was_indeed_in_Sarnia_more_direct
		: Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

	Qed.

End Fourth_version_of_MPP_three_times.

(** Coq allows us to abbreviate
(P : Prop) (Q : Prop) (R : Prop) (S : Prop): *)

Module Fifth_version_of_MPP_three_times.

	Theorem MPP_three_times
		(P Q R S : Prop)
		(Pr1 : P)
		(Pr2 : P -> Q)
		(Pr3 : Q -> R)
		(Pr4 : R -> S) : S.

	Proof.

		exact (Pr4 (Pr3 (Pr2 (Pr1)))).

	Qed.


	Theorem Patricia_was_indeed_in_Sarnia_more_direct
		: Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

	Qed.

End Fifth_version_of_MPP_three_times.

(**

So we have made a few changes to the Proof
of the generic MPP_three_times Theorem
and gotten it into a more direct form.

There is one final change that I want to
make before leaving this example.
We can put the premises in MPP_three_times
in any other order,
just as long as they come after the
declarations of P, Q, R, and S.

Putting Pr1 as the last premise may not make much difference,
but it enables a surprise that I will show in a second.

*)

Module Schönfinkel_version_of_MPP_three_times.

	Theorem MPP_three_times
		(P Q R S : Prop)
		(Pr2 : P -> Q)
		(Pr3 : Q -> R)
		(Pr4 : R -> S)
		(Pr1 : P) : S.

	Proof.

		exact (Pr4 (Pr3 (Pr2 (Pr1)))).

	Qed.

  (** Because the parameters to MPP_three_times
  are now in a different order, we have to
  change the order of the arguments in
	the Proof of the Theorem
  Patricia_was_indeed_in_Sarnia_more_direct: *)

	Theorem Patricia_was_indeed_in_Sarnia_more_direct
		: Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)
			(Patricia_is_indeed_prepared_to_make_marmalade)).

	Qed.

	(** As before, we have invoked
  MPP_three_times with eight arguments.
	We can check that MPP_three_times
  has eight parameters #&#8212;#
	P, Q, R, S, Pr2, Pr3, Pr4, and Pr1
  #&#8212;#
	and can therefore take eight arguments,
  like this: *)

	Check MPP_three_times
		: forall P Q R S : Prop,
			forall Pr2 : P -> Q,
			forall Pr3 : Q -> R,
			forall Pr4 : R -> S, forall Pr1 : P, S.

	(** But here's the surprise:
  MPP_three_times can also be
	invoked with only seven arguments! *)

	Check MPP_three_times
		: forall P Q R S : Prop,
			forall Pr2 : P -> Q,
			forall Pr3 : Q -> R,
			forall Pr4 : R -> S, P -> S.

	Theorem Patricia_was_in_Sarnia_if_she_can_now_make_marmalade
		: Patricia_is_prepared_to_make_marmalade
			-> Patricia_was_in_Sarnia.

	Proof.

		exact (MPP_three_times
			(Patricia_is_prepared_to_make_marmalade)
			(Patricia_has_bought_quinces)
			(Patricia_was_in_Robert's_store)
			(Patricia_was_in_Sarnia)
			(Patricia_needs_quinces_to_make_marmalade)
			(Patricia_always_buys_quinces_from_Robert)
			(Robert's_store_is_in_Sarnia)).

	Qed.

	(** What's going on?
  Those of you who know about Moses Schönfinkel
	and about the Curry-Howard Correspondence
  will have figured out
	how this is even possible,
  or will figure it out from these hints: *)

	Check MPP_three_times
		: forall P Q R S: Prop, (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.

	Check MPP_three_times
		: forall P Q R S: Prop, (P -> Q) -> (Q -> R) -> (R -> S) -> (P -> S).

End Schönfinkel_version_of_MPP_three_times.

(**

Whew!  This article has been long, but what have I accomplished?
I've managed to prove the example from the last article by making
the terse Theorem into a generic Theorem that can simplify the
verbose Theorem.  I've explored how to make the generic Theorem
shorter, one change at a time.  And I've managed to throw in
something to ponder.

For the next article, I plan to write about types in Coq. *)

(** ** References

#&#185;# Institut national de recherche en
sciences et technologies du numérique (Inria).
"The Coq Proof Assistant."
https://coq.inria.fr/

#&#178;# Hardegree, G. M. (1999)
"Symbolic Logic: A First Course."
McGraw-Hill College.
<https://courses.umass.edu/phil110-gmh/MAIN/IHome-5.htm>
The terse example is exercise 1 of section 5.22.

**)

End Article_3_Making_it_generic.

