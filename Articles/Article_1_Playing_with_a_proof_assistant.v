Module Article_1_Playing_with_a_proof_assistant.

(**
My software-development career began
forty years ago. I was still a schoolboy,
and the local high school offered a week-long
introduction to BASIC programming on their
Commodore PET computers. BASICally
(pun intended), arithmetic.

But there was one time when I was most
impressed with what a computer could do.
On a visit to the Open House event at the
University of Waterloo, my eventual alma mater,
I saw a computer that could do algebra and
even calculus. That is, I saw a computer
software package that could evaluate

    (a + b) * (c + d + e)

as equal to

    a * c + a * d + a * e + b * c + b * d + b * e

and could evaluate

    d (sin x) / (dx)

as equal to

    cos x.

The point of this introduction is that I've been
looking at some of the mathematical concepts
that I've learned over the years and just
exploring them.
But I need more than a computer to write test
programs that work with arithmetic.
I need to write mathematical proofs in such a way
that a computer check them.
Software that can check a mathematical proof
is called a proof assistant.

There are several proof assistants available.
The system that I am using is called Coq
(https://coq.inria.fr/) [1].
It is available for Windows and for Linux,
and if you have a Debian Linux distribution,
you can install Coq as a software package.

Strictly speaking, Coq is a proof assistant,
and its vernacular is not a programming language.
But one of the goals of Coq is to be a tool for
software development: in theory, your
professional programmer can write program code
in Coq's vernacular, then write proofs that the
program code is doing what it is supposed to do,
then have Coq validate all the proofs, then
finally have Coq extract the code expressed in
an actual programming language, like OCaml.

This article is not meant to be a tutorial
on Coq. Instead, it is an adventure of someone
who is learning Coq as he goes: figuring out
what works and what does not work, what looks
readable and what looks totally unreadable,
and trying to figure out how to get Coq to
check his proofs.

The first program that introduces a
computer language to new users, at least since
Kernighan and Richie's "The C Programming Language"
[2], involves the phrase "Hello, world".
Strictly speaking, Coq's vernacular is not
a programming language, but I should start
with a "Hello, world" example.
I have come up with this:
*)

Axiom Greeting : Prop.

Axiom Audience : Prop.

Axiom Hello : Audience -> Greeting.

Axiom World : Audience.

Theorem Hello_world : Greeting.

Proof.

    exact (Hello World).

Qed.

(**
If you have Coq installed,
you can run the Coq top-level program,
"coqtop", in a command-prompt window
and type each of these lines one at a time.
It would look like this:

[Example begins]

$ coqtop

Welcome to Coq 8.12.0 (November 2020)


Coq < Axiom Greeting : Prop.

Greeting is declared


Coq < Axiom Audience : Prop.

Audience is declared


Coq < Axiom Hello : Audience -> Greeting.

Hello is declared


Coq < Axiom World : Audience.

World is declared


Coq < Theorem Hello_world : Greeting.

1 subgoal


 ============================

 Greeting


Hello_world < Proof.


Hello_world < exact (Hello World).

No more subgoals.


Hello_world < Qed.


Coq < Quit.

$

[Example ends]

You could also save the above axioms and
theorem and proof in a text file named
"Article_1_Playing_with_a_proof_assistant.v",
then run "coqtop" with the "-l" option:

[Example begins]

coqtop -l Article_1_Playing_with_a_proof_assistant.v

[Example ends]

If there were any errors in the file,
you will get an error message and Coq quits.
If there are no errors - and there should be
no errors, for a reason that I will explain
in a moment - then it will display the
"Welcome" message and a "Coq <" prompt.

You can also open the Coq Integrated Development
Environment (or Coq IDE), copy the above commands
to the *scratch* file, save *scratch* as
"Article_1_Playing_with_a_proof_assistant.v",
and use the End command in the Navigation menu
to run the file.

In fact, I wrote THIS ENTIRE ARTICLE as
a file named
"Article_1_Playing_with_a_proof_assistant.v",
and ran the file with coqtop or the Coq IDE.
The text that you are reading appears between
the character sequence '(', '*', '*',
and the character sequence '*', ')'.
In general, text between
the character sequence '(', '*',
and the character sequence '*', ')'.
called a comment, and Coq ignores comments.

In a sense, this article has been verified
by Coq to be valid.  It is not unusual to
write articles that are Coq scripts: I am
following the example of Michael Nahas [3]
and writing the article as a script.
There is even an entire online book series,
"Software Foundations" [4],
which was written in the Coq vernacular
that have been verified and then published.

(The idea of publishing text as source code
is not new: Jim Welsh and Atholl Hay wrote
an entire book, "A Model Implementation of
Standard Pascal" [5], whose text was a single
source-code file with the human-readable text
in comments.
You could say, in the era of type-in programs
that were published in books and magazines,
that it was the ultimate type-in program.
But I do not recommend actually typing it in.)

So that's the first article.
For my second article, I plan on explaining
how to begin proving theorems in Coq.


* References:

[1] Institut national de recherche en
sciences et technologies du numérique (Inria).
"The Coq Proof Assistant."
https://coq.inria.fr/

[2] Kernighan, Brian, and Dennis Ritchie.
"The C Programming Language."
Prentice-Hall, 1978.

[3] Nahas, Michael.  "Mike Nahas's Coq Tutorial."
https://mdnahas.github.io/doc/nahas_tutorial.v

[4] Pierce, Benjamin C., et alia.  "Software Foundations."
Department of Computer and Information Science, University of Pennsylvania.
https://softwarefoundations.cis.upenn.edu/

[5] Welsh, Jim, and Atholl Hay.
"A Model Implementation of Standard Pascal."
Prentice-Hall (Simon & Schuster), 1986.

*)

End Article_1_Playing_with_a_proof_assistant.

