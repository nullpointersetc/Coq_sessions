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

    This article is not meant to be a tutorial
    on Coq.  Instead, it is an adventure of
    a Coq user who is learning as he goes.
    I have tried to make this accessible
    to a broad audience of users.

    The first program that introduces a
    computer language to new users,
    at least since Kernighan and Richie's
    "The C Programming Language" (1978),
    involves the phrase "Hello, world".
    I suppose that I should write a proof
    that involves that phrase in some
    way.  I came up with this: **)

Axiom Greeting : Prop.
Axiom Audience : Prop.
Axiom Hello : Audience -> Greeting.
Axiom World : Audience.
Theorem Hello_world : Greeting.
    Proof.
        exact (Hello World).
    Qed.

(** You can copy the above sequence of commands
    into a text file called "Hello_world.v"
    and run the file in coq using the command line: **)

   (* coqtop -l Hello_world.v *)

(** You can also open the Coq IDE
    (integrated development environment),
    write the above commands into the
    *scratch* file, save it as
    "Hello_world.v" and run the file.

    In fact, you can save **this entire article**
    as a text file called "Hello_world.v"
    and run the file with coqtop or the Coq IDE.
    Coq will ignore everything that appears
    between the characters '(' and '*'
    and the characters '*' and ')'.
    Some authors have adopted this practice
    because it means that a single file
    looks like an article to you, but it
    is also a proof that Coq can verify to
    be correct.

    So where do I go from here?
    I guess it would be to explain how the
    proof in this file actually works. **)

