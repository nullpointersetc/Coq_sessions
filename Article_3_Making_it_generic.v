(** 3. Making it generic **)

(** In the previous article, we had two proofs:
the terse proof and the verbose proof.
I have copied these proofs into this article,
but I have omitted all the comments from the terse example,
I have put the terse example inside a Module,
and I have put the verbose example inside a Section: **)

Module Terse_example.

Comments "Derived from Hardegree (1999) section 5.22, exercise 1.".

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


Section Verbose_example.

Axiom Patricia_is_prepared_to_make_marmalade : Prop.

Axiom Patricia_has_bought_quinces : Prop.

Axiom Patricia_was_in_Robert's_store : Prop.

Axiom Patricia_was_in_Sarnia : Prop.

Axiom Patricia_is_indeed_prepared_to_make_marmalade : Patricia_is_prepared_to_make_marmalade.

Axiom Patricia_needs_quinces_to_make_marmalade : Patricia_is_prepared_to_make_marmalade -> Patricia_has_bought_quinces.

Axiom Patricia_always_buys_quinces_from_Robert : Patricia_has_bought_quinces -> Patricia_was_in_Robert's_store.

Axiom Robert's_store_is_in_Sarnia : Patricia_was_in_Robert's_store -> Patricia_was_in_Sarnia.

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
 := Robert's_store_is_in_Sarnia (She_was_indeed_in_Robert's_store)
 : Patricia_was_in_Sarnia).

exact She_was_indeed_in_Sarnia.

Qed.

End Verbose_example.

(** I have more words to define before I proceed.

In the command "Theorem T1 : S", the Proposition S is called the "goal".
When you enter this command, Coq does not just blindly accept the
Theorem to be true.
Instead, immediately after the Theorem command,
Coq goes into "proof-editing mode";
it effectively demands that you prove your theorem.
You cannot normally leave proof-editing mode until you actually
write the Proof of the Theorem.  This mirrors how papers,
journals, and textbooks (for the college-and-university level,
at least) are written:
A theorem is stated, and it is immediately followed by its proof.

The "assert" command is called a "tactic".
A tactic in Coq is a step towards proving the goal.
Tactics in Coq usually start with lowercase letters instead of uppercase letters.
You can, and should, surmise that "exact" is also a tactic.

While in proof-editing mode, you must enter a tactic to proceed.
The tactic may introduce intermediate results that are known to
be true based on the current environment inside the proof
("assert" is such a tactic).  The tactic may also find the
goal within the current environment and state that the
goal has been achieved ("exact" is a tactic like this).
There are other tactics that add new goals and resolve other goals
in the middle of a proof.

That sounds like a lot of juggling for you and Coq to do,
and it is.  Coq is a "proof assistant" in that it keeps track
of everything that you've done, and it enforces that
every tactic that you use is valid.
(However, Coq is not a "theorem prover".
You cannot just give Coq a theorem and expect it
to automatically generate the proof.
This is actually a limit of computer science itself,
not of Coq specifically.

Now back to the examples.

The two examples are in fact similar:
Both of them declare, as Axioms, four Propositions.
Both of them declare, as a fifth Axiom,
that the first Proposition is true.
Both of them declare, as a sixth Axiom,
that the second Proposition is true
if the first Proposition is true.
Both of them declare, as a seventh Axiom,
that the third Proposition is true
if the second Proposition is true.
Both of them declare, as an eighth Axiom,
that the fourth Proposition is true
if the third Proposition is true.
Finally, both of them prove that the fourth Proposition is true
because of all eight Axioms.

The difference between the two examples is that
it is obvious from the terse example what the structure of the proof is,
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

Or ...

We might try to write the terse proof in such a way
that Coq is able to reuse it to prove the verbose theorem.

First off, we can restrict the letters P, Q, R, and S
so that they only apply to the Theorem and its proof,
by putting them in parentheses after the Theorem name
but before the ": S" part.  We can also put the
premises in parentheses after the Theorem name and
restrict them to the Theorem as well.
We do that and we get this: **)

Module First_version_of_MPP_three_times.

Theorem MPP_three_times
    (P : Prop)
    (Q : Prop)
    (R : Prop)
    (S : Prop)
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

(** Note: the order of the Axioms matters when using
the MPP_three_times Theorem.
The following Proof shows that putting the Axioms in the wrong
order will not work. **)

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

(** The Fail prefix is useful in scripts for writing
commands and tactics.

Normally, a command that Coq determines to be valid
is just executed and Coq continues,
but a command that Coq determines to be invalid
will cause Coq to stop and display an error message
that you will have to correct.
The same situation applies to tactics.

The Fail prefix works in the exact opposite way:
If Coq determines that the command prefixed by Fail
is invalid, Coq displays a diagnostic message
(the command has indeed failed) and continues.
But if the command prefixed by Fail actually is valid,
then Coq stops and displays an error message.
The same situation applies to a tactic with
the Fail prefix.

The Fail prefix is useful in scripts such as
this article.
I don't have to tell you that a command will fail;
I can write Fail command and Coq will verify
that the command does fail.

There are other changes we can make.
We don't really need to assert She_was_indeed_in_Sarnia separately;
we can just put the MPP_three_times term directly inside the
exact tactic: **)

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

(** Similarly, we don't really need to assert MPP7;
we can just replace MPP7 with the term Pr4 (MPP6)
inside the exact tactic: **)

Module Second_version_of_MPP_three_times.

Theorem MPP_three_times
    (P : Prop)
    (Q : Prop)
    (R : Prop)
    (S : Prop)
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

(** We don't even need to assert MPP6 either;
we can just replace MPP6 with the term Pr3 (MPP5)
inside the exact tactic: **)

Module Third_version_of_MPP_three_times.

Theorem MPP_three_times
    (P : Prop)
    (Q : Prop)
    (R : Prop)
    (S : Prop)
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

(** We don't even need to separately assert MPP5 either: **)

Module Fourth_version_of_MPP_three_times.

Theorem MPP_three_times
    (P : Prop)
    (Q : Prop)
    (R : Prop)
    (S : Prop)
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
    (P : Prop) (Q : Prop) (R : Prop) (S : Prop): **)

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


(** Coq allows us to abbreviate
    (P : Prop) (Q : Prop) (R : Prop) (S : Prop): **)

Module Sixth_version_of_MPP_three_times.

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

End Sixth_version_of_MPP_three_times.

(** There is one final change that I want to make before leaving
    this example:  We can put the premises in MPP_three_times
    in any other order, just as long as they follow the
    declarations of P, Q, R, and S.
    Of course, we now have to rewrite the exact tactic
    that uses MPP_three_times.

    Reordering the premises does not seem to make much difference.
    But putting Pr1 as the last premise actually makes a
    surprising change. **)

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


Theorem Patricia_was_indeed_in_Sarnia
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

(** As before, we have invoked MPP_three_times with eight arguments.
    We can check that MPP_three_times has eight parameters --
    P, Q, R, S, Pr2, Pr3, Pr4, and Pr1 --
    and can therefore take eight arguments, like this: *)

Check MPP_three_times
     : forall P Q R S : Prop,
       forall Pr2 : P -> Q, forall Pr3 : Q -> R,
       forall Pr4 : R -> S, forall Pr1 : P, S.

(** But here's the surprise: MPP_three_times can also be
    invoked with only seven arguments! *)

Check MPP_three_times
     : forall P Q R S : Prop,
       forall Pr2 : P -> Q, forall Pr3 : Q -> R,
       forall Pr4 : R -> S, P -> S.

Theorem Patricia_was_in_Sarnia_if_she_can_now_make_marmalade
    : Patricia_is_prepared_to_make_marmalade -> Patricia_was_in_Sarnia.

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

(** What's going on?  Those of you who know about Moses Schönfinkel
and about the Curry-Howard Correspondence will have figured out
how this is even possible, or will figure it out from these hints: *)

Check MPP_three_times
     : forall P Q R S: Prop, (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.

Check MPP_three_times
     : forall P Q R S: Prop, (P -> Q) -> (Q -> R) -> (R -> S) -> (P -> S).

End Schönfinkel_version_of_MPP_three_times.

(** Whew!  This article has been long, but what have I accomplished?
I've managed to prove the example from the last article by making
the terse Theorem into a generic Theorem that can simplify the
verbose Theorem.  I've explored how to make the generic Theorem
shorter, one change at a time.  And I've managed to throw in
something to ponder.

For the next article, I plan to write about types in Coq.

References

Hardegree, G. M. (1999) "Symbolic Logic: A First Course."
McGraw-Hill College.
<https://courses.umass.edu/phil110-gmh/MAIN/IHome-5.htm>

**)
