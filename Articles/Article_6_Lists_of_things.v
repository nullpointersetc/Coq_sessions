(** * Article 6. Lists of things.

#<blockquote>#
"I think I've figured out what's wrong with my friends."
#<br />&#8212; Starlight Glimmer&#185;</blockquote>#

#<blockquote>#
"I have a whole list of things that are wrong with your friends."
#<br />&#8212; Trixie&#178;</blockquote>#

As I write this article,
the summer festivals have returned to Victoria
Park in London, Ontario, after being cancelled
for the past two years due to lockdown.
(Actually, one festival did come back in 2021.)
And you will remember that we defined a date
type in the preceding article, so we can use
that type to represent the scheduled dates
of these festivals.

But the point of this article is to introduce
how to represent lists in Coq.
Many of these festivals are scheduled for
more than one day.  This scheduling motivates
what we will look at in this article:
a type that represents more than one date,
or if you will, a list of dates.

There is actually a type in Coq's standard
library that can be used to represent a lists.
Nevertheless, I want to develop my own versions
of lists.  I want to illustrate different
problems and how these are handled when we
eventually get to the actual definition in
the standard library.

As I have mentioned, the preceding article
declared a Date type.  Instead of repeating
that type here, I refer you to the preceding
article.  But I write each article in my Coq
series as a vernacular file, so I also
refer *Coq* to the preceding article as well:

*)
Add LoadPath "/home/darren/Coq_sessions/Articles" as Articles.

Load Article_5_Types_in_other_types.

Import Article_5_Types_in_other_types.

(** Now that we have our Date type, we can
start the code for this article. *)

Module Article_6_Lists_of_things.

(** I will be making many attempts to define a
type called List_of_dates.  So I need to
put each attempt into its own Module.
*)

(** ** First attempt: List of three dates *)

Module First_attempt.

    Inductive List_of_dates : Set :=
        Make_List (first : Date) (second : Date) (third : Date).

    (**

    We can use this type to represent the
    scheduled dates of any festival that lasts three days.
    One such festival is the Home County Folk Festival:

    *)

    Definition Home_County_2022 :=
        Make_List (Make_Date (Friday) (July) (fifteenth) (Year2022))
            (Make_Date (Saturday) (July) (sixteenth) (Year2022))
            (Make_Date (Sunday) (July) (seventeenth) (Year2022)).

    (**

    We can also define functions that fetch one of the
    dates out of the List_of_dates.  Make_List takes
    three parameters, but each definition is only
    interested in one of them; we use (_) to indicate
    each parameter that is not needed.

    *)

    Fail Definition First_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (first) (_) (_) => first
        end.

    Fail Definition Second_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (second) (_) => second
        end.

    Fail Definition Third_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (_) (third) => third
        end.

    (**

    These definitions all failed for a very odd reason:
    first, second, and third are already defined as
    constructors of the type Day_of_the_month,
    so instead of treating them as brand-new names
    for the new definitions, Coq tries use the
    existing names.
    Make_List takes complete dates, not days of the month only.
    So Coq complains in each case that it "Found a
    constructor of inductive type Day_of_the_Month
    while a constructor of Date is expected."

    The problem is that you, or somebody else,
    could add a name earlier in the file,
    or could add a name in another file that you have loaded
    (like Article_5_Types_in_other_types)
    and your Coq work fails.

    I believe that, in order for a technology to mature,
    it must be robust.  I have figured out a robust
    method of declaring that a name is to represent
    a parameter to a constructor, and that method is
    to write (_ as name) instead of just (name).
    That way, we can use the words first, second,
    third to mean full dates instead of days of the month:

    *)

    Definition First_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_ as first) (_) (_) => first
        end.

    Definition Second_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (_ as second) (_) => second
        end.

    Definition Third_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (_) (_ as third) => third
        end.

    Example July_17th
        : eq (Third_date (Home_County_2022))
        (Make_Date (Sunday) (July) (seventeenth) (Year2022)).
    Proof.
        unfold Home_County_2022.
        unfold Third_date.
        reflexivity.
    Qed.

    (** But this type can only represent
    three dates, no more (and no fewer). *)

    Fail Definition SunFest_2022 :=
        Make_List (Make_Date (Thursday) (July) (seventh) (Year2022))
            (Make_Date (Friday) (July) (eighth) (Year2022))
            (Make_Date (Saturday) (July) (ninth) (Year2022))
            (Make_Date (Sunday) (July) (tenth) (Year2022)).

    Fail Definition London_RibFest_2022 :=
        Make_List (Make_Date (Thursday) (July) (twenty_eighth) (Year2022))
            (Make_Date (Friday) (July) (twenty_ninth) (Year2022))
            (Make_Date (Saturday) (July) (thirtieth) (Year2022))
            (Make_Date (Sunday) (July) (thirty_first) (Year2022))
            (Make_Date (Monday) (August) (first) (Year2022)).

End First_attempt.

(**

The first problem we should fix is to allow
lists of more dates to be represented.
So let us abandon the first attempt, and
try to resolve this problem in the second attempt.

*)

(** ** Second attempt: Three or four or five dates *)

Module Second_attempt.

    Fail Inductive List_of_dates : Set :=
        Make_List (first : Date) (second : Date) (third : Date)
        | Make_List (first : Date)
            (second : Date) (third : Date) (fourth : Date)
        | Make_List (first : Date) (second : Date)
            (third : Date) (fourth : Date) (fifth : Date).

    (**

    Oops.  This failed because I added two more constructors
    and gave them the same name.  This is not allowed in
    Coq (unlike C++ and Java, where all constructors
    for a class have the same name, specifically,
    the name of the class being constructed).

    *)

    Inductive List_of_dates : Set :=
        Make_List (first : Date) (second : Date) (third : Date)
        | Make_List_of_4 (first : Date)
            (second : Date) (third : Date) (fourth : Date)
        | Make_List_of_5 (first : Date) (second : Date)
            (third : Date) (fourth : Date) (fifth : Date).

    Definition Home_County_2022 :=
        Make_List (Make_Date (Friday) (July) (fifteenth) (Year2022))
            (Make_Date (Saturday) (July) (sixteenth) (Year2022))
            (Make_Date (Sunday) (July) (seventeenth) (Year2022)).

    Definition First_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_ as first) (_) (_) => first
        | Make_List_of_4 (_ as first) (_) (_) (_) => first
        | Make_List_of_5 (_ as first) (_) (_) (_) (_) => first
        end.

    Definition Second_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (_ as second) (_) => second
        | Make_List_of_4 (_) (_ as second) (_) (_) => second
        | Make_List_of_5 (_) (_ as second) (_) (_) (_) => second
        end.

    Definition Third_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (_) (_ as third) => third
        | Make_List_of_4 (_) (_) (_ as third) (_) => third
        | Make_List_of_5 (_) (_) (_ as third) (_) (_) => third
        end.

    Definition SunFest_2022 :=
        Make_List_of_4 (Make_Date (Thursday) (July) (seventh) (Year2022))
            (Make_Date (Friday) (July) (eighth) (Year2022))
            (Make_Date (Saturday) (July) (ninth) (Year2022))
            (Make_Date (Sunday) (July) (tenth) (Year2022)).

    Definition London_RibFest_2022 :=
        Make_List_of_5 (Make_Date (Thursday) (July) (twenty_eighth) (Year2022))
            (Make_Date (Friday) (July) (twenty_ninth) (Year2022))
            (Make_Date (Saturday) (July) (thirtieth) (Year2022))
            (Make_Date (Sunday) (July) (thirty_first) (Year2022))
            (Make_Date (Monday) (August) (first) (Year2022)).

    Example July_17th
        : eq (Third_date (Home_County_2022))
        (Make_Date (Sunday) (July) (seventeenth) (Year2022)).
    Proof.
        unfold Home_County_2022.
        unfold Third_date.
        reflexivity.
    Qed.

    (**

    Everything we tried in the first attempt
    now works in the second attempt.
    But if we need a list of two dates,
    or a list of more than five dates,
    we can't represent them in the current List_of_dates
    type.  We are right back where we started.
    The obvious solution would be to add even more
    ways to construct a list, and we would have to
    modify First_date, Second_date, and Third_date.

    Another problem is also evident in the definitions
    of First_date, Second_date, and Third_date:
    why did we not define Fourth_date and Fifth_date?
    We could try defining them like this:

    *)

    Fail Definition Fourth_date (dates : List_of_dates) : Date
        := match dates
        with Make_List_of_4 (_) (_) (_) (_ as fourth) => fourth
        | Make_List_of_5 (_) (_) (_) (_ as fourth) (_) => fourth
        end.

    Fail Definition Fifth_date (dates : List_of_dates) : Date
        := match dates
        with Make_List_of_5 (_) (_) (_) (_) (_ as fifth) => fifth
        end.

    (**

    It does not make sense to define a "Fourth_date"
    for a list of only three dates.
    But Coq does not allow the above definition of Fourth_date.
    It makes sense when you consider that Fourth_date
    must have the type "List_of_dates -> Date",
    or equivalently, "forall (dates : List_of_Dates), Date".
    The bottom line is, you have to define Fourth_date
    for all possible List_of_dates, even the ones with
    three dates.  ("Fifth_date" has the same issue;
    the only way to define Fifth_date for a list is when
    the list has five dates.)

    The simplest solution is to just define Fourth_date
    and Fifth_date incorrectly for lists of three dates
    (and Fifth_date for lists of four dates):

    *)

    Definition Fourth_date (dates : List_of_dates) : Date
        := match dates
        with Make_List_of_4 (_) (_) (_) (_ as fourth) => fourth
        | Make_List_of_5 (_) (_) (_) (_ as fourth) (_) => fourth
        | Make_List (_) (_) (_ as third) => third
        end.

    Definition Fifth_date (dates : List_of_dates) : Date
        := match dates
        with Make_List_of_5 (_) (_) (_) (_) (_ as fifth) => fifth
        | Make_List (_) (_) (_ as third) => third
        | Make_List_of_4 (_) (_) (_) (_ as fourth) => fourth
        end.

End Second_attempt.

(** ** Third attempt: Making a bigger list from a smaller list

The ideas behind the third attempt are quite simple:

    - We can make a list of two dates.

    - We can take a list of two dates and put it
      together with another date to make a list
      of three dates.

    - We can take a list of three dates and put it
      together with another date to make a list
      of four dates.

    - And so on, and so on, and so on.

We can express these ideas more simply,
and more accurately, in these two ideas:

    - We can make a list of two dates.

    - We can take an existing list and
      put it together with another date
      to make a list that has one more date
      that the existing list.

So here we go:

*)

Module Third_attempt.

    Inductive List_of_dates : Set :=
        cons' (head : Date) (tail : Date)
        | cons (head : List_of_dates) (tail : Date).

    (** (There is a tradition where "cons"
    is the name of the operation that
    constructs a list.) *)

    Definition Home_County_2022 :=
        cons (cons' (Make_Date (Friday) (July) (fifteenth) (Year2022))
                (Make_Date (Saturday) (July) (sixteenth) (Year2022)))
            (Make_Date (Sunday) (July) (seventeenth) (Year2022)).

    Definition SunFest_2022 :=
        cons (cons (cons' (Make_Date (Thursday) (July) (seventh) (Year2022))
                    (Make_Date (Friday) (July) (eighth) (Year2022)))
                (Make_Date (Saturday) (July) (ninth) (Year2022)))
            (Make_Date (Sunday) (July) (tenth) (Year2022)).

    Definition London_RibFest_2022 :=
        cons (cons (cons (cons'
                        (Make_Date (Thursday) (July) (twenty_eighth) (Year2022))
                        (Make_Date (Friday) (July) (twenty_ninth) (Year2022)))
                    (Make_Date (Saturday) (July) (thirtieth) (Year2022)))
                (Make_Date (Sunday) (July) (thirty_first) (Year2022)))
            (Make_Date (Monday) (August) (first) (Year2022)).

End Third_attempt.

Module Fourth_attempt.

    Inductive List_of_dates : Set :=
        cons' (head : Date) (tail : Date)
        | cons (head: Date) (tail : List_of_dates).

    Definition Home_County_2022 :=
        cons (Make_Date (Friday) (July) (fifteenth) (Year2022))
             (cons' (Make_Date (Saturday) (July) (sixteenth) (Year2022))
                    (Make_Date (Sunday) (July) (seventeenth) (Year2022))).

    Definition SunFest_2022 :=
        cons (Make_Date (Thursday) (July) (seventh) (Year2022))
             (cons (Make_Date (Friday) (July) (eighth) (Year2022))
                   (cons' (Make_Date (Saturday) (July) (ninth) (Year2022))
                          (Make_Date (Sunday) (July) (tenth) (Year2022)))).

    Definition London_RibFest_2022 :=
        cons (Make_Date (Thursday) (July) (twenty_eighth) (Year2022))
            (cons (Make_Date (Friday) (July) (twenty_ninth) (Year2022))
                 (cons (Make_Date (Saturday) (July) (thirtieth) (Year2022))
                      (cons' (Make_Date (Sunday) (July) (thirty_first) (Year2022))
                          (Make_Date (Monday) (August) (first) (Year2022))))).

End Fourth_attempt.

(** ** References

1. Haber, Josh, and Michael Vogel.
"To Where and Back Again &mdash; Part 1".
Episode 142 of "My Little Pony: Friendship is Magic."
Vancouver, B.C.: DHX Studios, 2016.  Starlight Glimmer voiced by Kelly Sheridan.

2. Ibid. Trixie voiced by Kathleen Barr.
*)

End Article_6_Lists_of_things.

