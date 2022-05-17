(** Playing with ... a proof assistant **)

(** My software-development career began
    forty years ago.  I was still a schoolboy,
    and the local high school offered a
    week-long introduction to BASIC programming
    on their Commodore PET computers.
    BASICally (pun intended), arithmetic.

    But the time I was most impressed with what
    a computer could do was when I saw one
    that could do algebra and even calculus.
    That is, I saw a computer software package
    that could evaluate

    (a + b) (c + d + e)

    with

    ac + ad + ae + bc + bd + be

    and could evaluate

    d (sin x) / (dx)

    as

    cos x.

    The point of this introduction is that
    I've been looking at some of the
    mathematical concepts I've learned
    over the years and just exploring them.
    But I need more than a computer to
    write test programs that work with
    arithmetic.  I need to write
    mathematical proofs in such a way
    that a computer check them.
    The software that can check
    a mathematical proof is called
    a proof assistant.

    There are several proof assistants
    available.

    The system that I am using is called
    Coq (https://coq.inria.fr/).
    It is available for Windows and for Linux,
    and if you have a Debian Linux distribution,
    you can install Coq as a software package.

    Strictly speaking, Coq is a proof
    assistant, and its vernacular is not
    strictly speaking a programming language.
    But one of the goals of Coq is to be a
    tool for software development: in theory,
    your professional programmer can write
    program code in Coq's vernacular,
    then write proofs that the program code
    is doing what it is supposed to do,
    then have Coq validate all the proofs,
    then finally have Coq extract the code
    expressed in an actual programming
    language, like OCaml.

    This article is not meant to be a tutorial
    on Coq.  Instead, it is an adventure of
    someone who is learning Coq as he goes:
    figuring out what works and what does not work,
    what looks readable and what looks totally
    unreadable, and trying to figure out
    how to get Coq to do a Coq user who is learning as he goes.
    I have tried to make this accessible
    to a broad audience of users.

    The first program that introduces a
    computer language to new users,
    at least since Kernighan and Richie's
    "The C Programming Language" (1978),
    involves the phrase "Hello, world".
    Strictly speaking, Coq's vernacular is
    not a programming language, but I should
    start with a "Hello, world" example.
    I have come up with this: **)

Axiom Greeting : Prop.
Axiom Audience : Prop.
Axiom Hello : Audience -> Greeting.
Axiom World : Audience.
Theorem Hello_world : Greeting.
    Proof.
        exact (Hello World).
    Qed.

(** If you have Coq installed, you can run
    the Coq top-level program, "coqtop",
    in a command-prompt window and
    type each of these lines one at a time.
    It would look like this: **)

(**** Example begins ****

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

**** Example ends ****)

(** You could also save the above
    Axioms and Theorem and Proof in
    a text file named "Hello_world.v",
    then run "coqtop" with the "-l" option: **)

(**** Example begins ****

coqtop -l Hello_world.v

**** Example ends ****)

(** If there were any errors in the file,
    you will get an error message and Coq quits.

    If there are no errors - and there
    should be no errors, for a reason that
    I will explain in a moment - then
    it will display the "Welcome" message
    and a "Coq <" prompt.

    You can also open the Coq Integrated
    Development Environment (or Coq IDE),
    copy the above commands to the
    *scratch* file, save *scratch* as
    "Hello_world.v", and use the End command
    in the Navigation menu to run the file.

    In fact, you can copy the text of
    **this entire article** into *scratch*,
    save it as "Hello_world.v"
    and run the file with coqtop or the Coq IDE.
    Any text that appears between
    the characters '(' and '*'
    and the characters '*' and ')'
    is called a comment,
    and Coq ignores comments.
    In a sense, this article has been
    verified by Coq to be valid.

    It is not unusual to write articles
    that are Coq scripts.  There is
    even an entire online book series,
    "Software Foundations"
    (https://softwarefoundations.cis.upenn.edu/)
    (Department of Computer
    and Information Science,
    University of Pennsylvania)
    which was written in the Coq vernacular
    that have been verified and then published.

    So that's the first article.
    For my second article, I plan on explaining
    how to begin proving theorems in Coq. **)
