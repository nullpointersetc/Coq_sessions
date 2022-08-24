(** printing  ->  #&#45;&#62;# **)
(** printing  =>  #&#61;&#62;# **)
(** printing  forall  #forall# **)
(** * Article 6. Lists of things. *)

(** As I write this article,
some of the annual festivals have returned to
London, Ontario, after being cancelled
for the past two years due to lockdown.
And you will remember that we defined a date
type in the preceding article, so we can use
that type to represent the scheduled dates
of these festivals.

Many of these festivals are scheduled for
more than one day.  This scheduling motivates
what we will look at in this article:
a type that represents more than one date,
or if you will, a list of dates.

The point of this article is to introduce
how to represent lists in #Coq.&#185;#
There is actually a type in Coq's standard
library that can be used to represent a list.
Nevertheless, I want to develop my own versions
of lists.  I want to illustrate different
problems and how these are handled when we
eventually get to the actual definition in
the standard library.

As I have mentioned, the preceding article
declared a Date type.  Instead of repeating
that type here, I refer you to the preceding
#article.&#178;#  But I write each article in my Coq
series as a vernacular file, so I also
refer #<em>Coq</em># to the preceding article as well: **)

Load Article_5_Types_in_other_types.

Import Article_5_Types_in_other_types.

(** Now that we have our Date type, we can
start the code for this article. *)

Module Article_6_Lists_of_things.

(** I will be making many attempts to define a
type called List_of_dates.  So I need to
put each attempt into its own Module. *)

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

    Definition First_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (the_first) (_) (_) => the_first
        end.

    Definition Second_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (the_second) (_) => the_second
        end.

    Fail Definition Third_date (dates : List_of_dates) : Date
        := match dates
        with Make_List (_) (_) (third) => third
        end.

    (** The last definition fails for a very odd reason:
    third is already defined as constructors of the type
    Day_of_the_month, so instead of treating third as
    a brand-new name in the pattern, Coq tries use the
    existing name.  [Make_List] can only be constructed
    with three Dates, but [third] is already
    a [Day_of_the_Month].

    One of the problems with this failed definition
    is the error message that Coq displays:
    [Found a constructor of inductive type Day_of_the_Month
    while a constructor of Date is expected.]
    This is a common problem with software development,
    or rather with software developers.
    The programmer knows what's wrong with what I typed,
    but the programmer's message is what a programmer
    would write.  The user who's trying to learn Coq,
    however, might find this message confusing,
    and probably find it unfriendly as well.
    As a software developer "on the other side",
    as it were, I have a lesson to learn here:
    always try to make the error message as simple
    and clear as possible.

    The other problem with this code is that it
    depends on the code that I already imported earlier.
    Sure, I could change the code to use a new name
    like [the_third].  But the writer of the code
    that got included by
    [Load Article_5_Types_in_other_types]
    and [Import Article_5_Types_in_other_types]
    could change that code to define [the_third,]
    or [the_first] or [the_second,] and then this
    Coq file won't compile any more.
    I have figured out a more robust method of declaring
    a name that represents part of a pattern, and that
    is to write [_ as third] instead of just [third]
    in the pattern.

    *)

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

    (** But this type can only represent three dates.
    It cannot represent four dates
    and it cannot represent five dates. *)

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

    (** So let us abandon the first attempt,
    and try to write a type that can represent
    four dates or five dates, instead of just three. *)

End First_attempt.

(** ** Second attempt: Three or four or five dates *)

Module Second_attempt.

    Fail Inductive List_of_dates : Set :=
        Make_List (first : Date) (second : Date) (third : Date)
        | Make_List (first : Date)
            (second : Date) (third : Date) (fourth : Date)
        | Make_List (first : Date) (second : Date)
            (third : Date) (fourth : Date) (fifth : Date).

    (**  Oops.  This failed because I tried to make a type
    with three constructors and I gave them all the same name.
    This is not allowed in Coq (unlike C++ and Java,
    where all constructors for a class must have the same name
    as the class to be constructed).
    So I'll use different names: *)

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

    (** Everything I tried in the first attempt now works
    in the second attempt. But if we need a list of two dates,
    or a list of six dates, we can't represent them in the
    current List_of_dates type.  I am right back where we started.
    The obvious solution would be to add even more
    ways to construct a list, and we would have to
    modify First_date, Second_date, and Third_date.

    Another problem is also evident from the definitions of
    First_date, Second_date, and Third_date:
    we also need a Fourth_date and Fifth_date: *)

    Fail Definition Fourth_date (dates : List_of_dates) : Date
        := match dates
        with Make_List_of_4 (_) (_) (_) (_ as fourth) => fourth
        | Make_List_of_5 (_) (_) (_) (_ as fourth) (_) => fourth
        end.

    Fail Definition Fifth_date (dates : List_of_dates) : Date
        := match dates
        with Make_List_of_5 (_) (_) (_) (_) (_ as fifth) => fifth
        end.

    (** Coq replies with another error message:
    [Non exhaustive pattern-matching:
    no clause found for pattern Make_List _ _ _].

    It does not make sense to define [Fourth_date]
    for a list of only three dates.
    But in Coq, the type of [Fourth_date] is
    [forall (dates : List_of_Dates), Date.]
    As the word "forall" suggests, [Fourth_date]
    must be able to take any List_of_Dates,
    no matter if it has three dates or four dates
    or five dates.  [Fifth_date] has the same problem;
    the only sensible lists it can apply to are
    those with five dates.

    There are ways of declaring [Fourth_date]
    so that you can only apply it to lists of four dates
    and to lists of five date.
    But for the present, I am going to change
    the meaning of [Fourth_date] slightly
    for all possible List_of_Dates.
    For the lists of four dates and for the lists of
    five dates, the [Fourth_date] is "some date."
    For the lists of three dates, the [Fourth_date]
    will be "not a date".
    I can define a type that can be "some date"
    or "not a date": *)

    Inductive Date_or_No_Date : Set :=
        Some_Date (date : Date)
        | No_Date.

    (* Now [Fourth_date] can be defined: *)

    Definition Fourth_date (dates : List_of_dates)
        : Date_or_No_Date
        := match dates
        with Make_List_of_4 (_) (_) (_) (_ as fourth) => Some_Date (fourth)
        | Make_List_of_5 (_) (_) (_) (_ as fourth) (_) => Some_Date (fourth)
        | Make_List (_) (_) (_) => No_Date
        end.

    (* Now I can also define [Fifth_date:] *)

    Definition Fifth_date (dates : List_of_dates)
        : Date_or_No_Date
        := match dates
        with Make_List_of_5 (_) (_) (_) (_) (_ as fifth) => Some_Date (fifth)
        | Make_List (_) (_) (_) => No_Date
        | Make_List_of_4 (_) (_) (_) (_) => No_Date
        end.

    Example July_10th
        : eq (Fourth_date (SunFest_2022))
        (Some_Date (Make_Date (Sunday) (July) (tenth) (Year2022))).
    Proof.
        unfold SunFest_2022.
        unfold Fourth_date.
        reflexivity.
    Qed.

    Example August_1st
        : eq (Fifth_date (London_RibFest_2022))
        (Some_Date (Make_Date (Monday) (August) (first) (Year2022))).
    Proof.
        unfold London_RibFest_2022.
        unfold Fifth_date.
        reflexivity.
    Qed.

    (** Everything works so far.  Now, I'm going to
    try solving the problem about lists of two dates,
    and lists of six dates, and so on. *)

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

    - We can take a list of four dates and put it
      together with another date to make a list
      of five dates.

    - And so on.

We can collapse the construction of lists of three dates
or more into a single idea:

    - We can take an existing list and
      put it together with another date
      to make a list that has one more date
      that the existing list.

*)

Module Third_attempt.

    Inductive List_of_dates : Set :=
        cons2 (head : Date) (tail : Date)
        | cons (head : List_of_dates) (tail : Date).

    (** (Using the name [cons] as the name of the constructor
    of a larger list from a smaller list dates back to LISP.)

    This is my first truly inductive type in this series.
    What makes this List_of_dates inductive is that
    one of the constructors takes a parameter of the
    same type as the type we are constructing.
    In particular,
    to make a list of three dates, you must use
    the [cons] constructor with an existing list
    of two dates and with the third date.
    To make a list of four dates, you must use
    the [cons] constructor with an existing list
    of three dates and with the fourth date. *)

    Definition Home_County_2022 :=
        cons (cons2 (Make_Date (Friday) (July) (fifteenth) (Year2022))
                (Make_Date (Saturday) (July) (sixteenth) (Year2022)))
            (Make_Date (Sunday) (July) (seventeenth) (Year2022)).

    Definition SunFest_2022 :=
        cons (cons (cons2 (Make_Date (Thursday) (July) (seventh) (Year2022))
                    (Make_Date (Friday) (July) (eighth) (Year2022)))
                (Make_Date (Saturday) (July) (ninth) (Year2022)))
            (Make_Date (Sunday) (July) (tenth) (Year2022)).

    Definition London_RibFest_2022 :=
        cons (cons (cons (cons2
                        (Make_Date (Thursday) (July) (twenty_eighth) (Year2022))
                        (Make_Date (Friday) (July) (twenty_ninth) (Year2022)))
                    (Make_Date (Saturday) (July) (thirtieth) (Year2022)))
                (Make_Date (Sunday) (July) (thirty_first) (Year2022)))
            (Make_Date (Monday) (August) (first) (Year2022)).

    Definition Western_Fair_2022 :=
        cons (cons (cons (cons (cons (cons (cons (cons (cons2
        (Make_Date (Friday)    (September) (ninth)          (Year2022))
        (Make_Date (Saturday)  (September) (tenth)          (Year2022)))
        (Make_Date (Sunday)    (September) (eleventh)       (Year2022)))
        (Make_Date (Monday)    (September) (twelfth)        (Year2022)))
        (Make_Date (Tuesday)   (September) (thirteenth)     (Year2022)))
        (Make_Date (Wednesday) (September) (fourteenth)     (Year2022)))
        (Make_Date (Thursday)  (September) (fifteenth)      (Year2022)))
        (Make_Date (Friday)    (September) (sixteenth)      (Year2022)))
        (Make_Date (Saturday)  (September) (seventeenth)    (Year2022)))
        (Make_Date (Sunday)    (September) (eighteenth)     (Year2022)).

    (* Now we can make lists of two dates.
    ** But we need a different defintion for
    ** [First_date] and [Second_date].
    ** It's easy to define them for a list of two dates
    ** (constructed with [cons2]):  just pull out the date.
    ** But for a longer list, we need to pull out the smaller list
    ** and then pull the date from the smaller list.
    **
    ** This means that we need to define First_date recursively,
    ** and the definition of a recursive function must use the
    ** command Fixpoint instead of Definition.
    ** (I don't know why the command is called Fixpoint.) *)

    Fixpoint First_date (dates : List_of_dates) : Date
        := match dates
        with cons2 (_ as first) (_) => first
        | cons (_ as first_few) (_) => First_date (first_few)
        end.

    Fixpoint Second_date (dates : List_of_dates) : Date
        := match dates
        with cons2 (_) (_ as second) => second
        | cons (_ as first_few) (_) => Second_date (first_few)
        end.

    (* But [Third_date] now has to be more complicated,
    ** because for lists of two dates, [Third_date]
    ** must be [No_Date.] *)

    Inductive Date_or_No_Date : Set :=
        Some_Date (date : Date)
        | No_Date.

    Fixpoint Third_date (dates : List_of_dates)
        : Date_or_No_Date
        := match dates
        with cons2 (_) (_) => No_Date
        | cons (cons2 (_) (_)) (_ as third) => Some_Date (third)
        | cons (_ as first_few) (_) => Third_date (first_few)
        end.

    Fixpoint Fourth_date (dates : List_of_dates)
        : Date_or_No_Date
        := match dates
        with cons2 (_) (_) => No_Date
        | cons (cons2 (_) (_)) (_) => No_Date
        | cons (cons (cons2 (_) (_)) (_)) (_ as fourth)
            => Some_Date (fourth)
        | cons (_ as first_few) (_) => Fourth_date (first_few)
        end.

    Fixpoint Fifth_date (dates : List_of_dates)
        : Date_or_No_Date
        := match dates
        with cons2 (_) (_) => No_Date
        | cons (cons2 (_) (_)) (_) => No_Date
        | cons (cons (cons2 (_) (_)) (_)) (_) => No_Date
        | cons (cons (cons (cons2 (_) (_)) (_)) (_)) (_ as fifth)
            => Some_Date (fifth)
        | cons (_ as first_few) (_) => Fifth_date (first_few)
        end.

    (* And to make sure that these work: *)

    Example July_17th
        : eq (Third_date (Home_County_2022))
        (Some_Date (Make_Date (Sunday) (July) (seventeenth) (Year2022))).
    Proof.
        unfold Home_County_2022.
        unfold Third_date.
        reflexivity.
    Qed.

    Example July_10th
        : eq (Fourth_date (SunFest_2022))
        (Some_Date (Make_Date (Sunday) (July) (tenth) (Year2022))).
    Proof.
        unfold SunFest_2022.
        unfold Fourth_date.
        reflexivity.
    Qed.

    Example August_1st
        : eq (Fifth_date (London_RibFest_2022))
        (Some_Date (Make_Date (Monday) (August) (first) (Year2022))).
    Proof.
        unfold London_RibFest_2022.
        unfold Fifth_date.
        reflexivity.
    Qed.

End Third_attempt.

(** This article is already long, and I'm not even
close to where I wanted to be at the end of it.
I had planned on changing the type definition
to be more focused on the start of the list
instead of the end of the list.
I had planned on handling the case where,
instead of a list of dates, you only have one date.
I had planned on handling the case where,
instead of a date or a list of dates, you have no dates.
But all of these will have to wait until the next article. *)

(** ** References

#&#185;# Institut national de recherche en
sciences et technologies du numérique (Inria).
"The Coq Proof Assistant."
https://coq.inria.fr/

#&#178;# "Article 5. Types in other types."

*)

End Article_6_Lists_of_things.

