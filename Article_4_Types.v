(** 4. Simple types and simple functions *)
Module Four.

(** I find it quite hard to explain what
a type is.  I could simply say that a
type is a set of values, but that is so
vague.  So instead, I will pose a couple
of examples:

Here are two types that should be familiar
to many people: the days of the week and the
months of the year according to the Gregorian
calendar: *)

Inductive Day_of_the_Week : Set :=
    Monday | Tuesday | Wednesday
    | Thursday | Friday
    | Saturday | Sunday.

Inductive Month_of_the_Year : Set :=
    January | February | March
    | April | May | June
    | July | August | September
    | October | November | December.

(** For now, you can ignore that the command
that defines a type is called "Inductive",
because these types don't come to my mind
as being inductive.

Each of the names in a type is called a
constructor.  The type Days_of_the_Week
has seven constructors, each of which
has the English name of a day of the week.
The type Months_of_the_Year has twelve
constructors, each of which has the
English name of a month of the year.

So what can you do with these types?
You can declare variables of these types: *)

Section Vars.
Variable payday : Day_of_the_Week.
Variable festival_day : Day_of_the_Week.
End Vars.

(** You can give new names to the constructors.
For example, you can define the French names
as aliases for the days of the week: *)

Definition lundi : Day_of_the_Week := Monday.
Definition mardi : Day_of_the_Week := Tuesday.
Definition mercredi : Day_of_the_Week := Wednesday.
Definition jeudi : Day_of_the_Week := Thursday.
Definition vendredi : Day_of_the_Week := Friday.
Definition samedi : Day_of_the_Week := Saturday.
Definition dimanche : Day_of_the_Week := Sunday.

(** However, if you try to declare aliases
of one type to be constructors of another type,
Coq will catch the error.  Declaring the
Spanish names of the days of the week
will not work if done this way: *)

Fail Definition lunes : Month_of_the_Year := Monday.
Fail Definition martes : Month_of_the_Year := Tuesday.
Fail Definition miércoles : Month_of_the_Year := Wednesday.
Fail Definition jueves : Month_of_the_Year := Thursday.
Fail Definition viernes : Month_of_the_Year := Friday.
Fail Definition sabado : Month_of_the_Year := Saturday.
Fail Definition domingo : Month_of_the_Year := Sunday.

(** Each of the above will give a message
similar to: *)

(*
The command has indeed failed with message:
The term "Monday" has type "Day_of_the_Week" while it is expected to have type "Month_of_the_Year".
*)

(** While you could fix these by changing the
name of the type being referred to,
there is a simpler solution: Don't mention
the type at all, and let Coq figure it out. *)

Definition lunes := Monday.
Definition martes := Tuesday.
Definition miércoles := Wednesday.
Definition jueves := Thursday.
Definition viernes := Friday.
Definition sabado := Saturday.
Definition domingo := Sunday.

(** Just as the names of the days of the
week are fixed, the order is also fixed.
The day after Monday will always be
Tuesday, the day after Friday will always
be Saturday, and so on.  We can define
this order like this: *)

Definition Day_after (d : Day_of_the_Week)
    : Day_of_the_Week
    := match d
    with Monday => Tuesday
    | Tuesday => Wednesday
    | Wednesday => Thursday
    | Thursday => Friday
    | Friday => Saturday
    | Saturday => Sunday
    | Sunday => Monday
    end.

(** This kind of definition is called a function.
This function takes a parameter,
which is called d inside the function,
and which must be a Day_of_the_Week.
The function returns a Day_of_the_Week.

We can use this function by naming Day_after
and naming the Day_of_the_Week, like in
this defintion of the German name for
Monday as the day after Sunday: *)

Definition Montag := Day_after (Sunday).

(** At this point, allow me to add one more term.
I call term after the function name,
which in this case is Sunday,
an argument.  In this case, the argument
Sunday is represented in the function Day_after
by the parameter d.  (Some computer programmers
would call d a formal parameter
or a formal argument,
and call Sunday an actual parameter or an
actual argument.  But I prefer to call
a formal parameter simply a parameter,
and to call an acutal parameter an argument.

I also prefer to put the argument in parentheses,
but Coq allows you to omit them if the argument
is simply a name: *)

Definition Dienstag := Day_after Monday.

(** You can even use the aliases we defined
earlier: *)

Definition Mittwoch := Day_after (mardi).
Definition Donnerstag := Day_after (Mittwoch).

(** Finally, you can take the result of
a function and use it as an argument of
a function.  So "two days after" a day
is the day after the day after the original day: *)

Definition Freitag :=
    Day_after (Day_after (Mittwoch)).

Definition Samstag :=
    Day_after (Day_after (Day_after (Mittwoch))).

Definition Sonnabend :=
    Day_after (Day_after (Day_after Mittwoch)).

Definition Sonntag :=
    Day_after (Day_after
    (Day_after (Day_after (Mittwoch)))).

(** We can also define the inverse function
Day_before: *)

Fail Definition Day_before (d : Day_of_the_Week) :=
    match d
    with Monday => Sunday
    | Tuesday => Monday
    | Wednesday => Tuesday
    | Thursday => Wednesday
    | Saturday => Friday
    | Sunday => Saturday
    end.

(* The command has indeed failed with message:
   Non exhaustive pattern-matching: no clause found for pattern
   Friday *)

(** Oops. I forgot to specify what the
day before Friday is, and Coq noticed it.
This is an important point: A function
with a parameter must give a result for
every possible value of the parameter,
that is, every possible value of the type
of the parameter.  So let's fix it: *)  

Definition Day_before (d : Day_of_the_Week) :=
    match d
    with Monday => Sunday
    | Tuesday => Monday
    | Wednesday => Tuesday
    | Thursday => Wednesday
    | Friday => Thursday
    | Saturday => Friday
    | Sunday => Saturday
    end.

(** Of course, we have all these definitions now,
but we only have faith that they all work as expected.
But Coq not only allows us to make definitions, it
also allows us to make theorems on the defintions
to prove that they are as expected.  To do this,
I'm going to have to use terms and tactics
that I don't plan on explaining fully at this time,
so bear with me.

First, the term eq (x) (y) is a Prop
that means that x is equal to y.
In ordinary algebra,
x is called the left-hand side
and y is called the right-hand side..

Second, the tactic "reflexivity" means that
the goal we are trying to prove is an eq,
and the two terms that follow eq are equal.

Third, the tactic "rewrite -> R1 in R2"
means that R1 is an eq, and if Coq finds
the first term of the eq in R2, then it is
to substitute the second term of R1 in R2.
In this case, R2 is
Wednesday = Day_after (Tuesday),
and Tuesday is the left-hand side of R1.
Rewrite changes the Tuesday in R2
to be the right-hand side of R1, which is
Day_after (Monday).
So R2 becomes
Wednesday = Day_after (Day_after (Monday)).
*)

Theorem Two_days_after_Monday :
    Wednesday = Day_after (Day_after (Monday)).
Proof.
    assert (R1 : Tuesday = Day_after (Monday)) by reflexivity.
    assert (R2 : Wednesday = Day_after (Tuesday)) by reflexivity.
    rewrite -> R1 in R2.
    exact R2.
Qed.

Theorem Two_days_after_Tuesday :
    Thursday = Day_after (Day_after (Tuesday)).
Proof.
    assert (P2 : Thursday =
        Day_after (Day_after (Tuesday)))
        by reflexivity.
    exact P2.
Qed.

(** There are two more assertions that I want to
prove before closing this article.

The first assertion is that there are only
seven days of the week (not, for example, eight).
For this proof, I've used "or": or A B is a Prop
that means either A is true or B is true.
The tactic "left" means that we only want to prove A
in order to prove or A B.
Similarly, the tactic "right" means that we only want to prove B
in order to prove or A B.
Finally, we can have an anonymous function
(a function without a name) using "fun".
*)

Theorem Day_must_be_MTWTFSS :
    forall d : Day_of_the_Week,
    or (or (or (or (or (or (d = Monday) (d = Tuesday))
    (d = Wednesday)) (d = Thursday))
    (d = Friday)) (d = Saturday)) (d = Sunday).
Proof.
    assert (Mon : or (or (or (or (or (or
        (Monday = Monday) (Monday = Tuesday))
        (Monday = Wednesday)) (Monday = Thursday))
        (Monday = Friday)) (Monday = Saturday))
        (Monday = Sunday))
        by (left; left; left; left; left; left; reflexivity).
    assert (Tue : or (or (or (or (or (or
        (Tuesday = Monday) (Tuesday = Tuesday))
        (Tuesday = Wednesday)) (Tuesday = Thursday))
        (Tuesday = Friday)) (Tuesday = Saturday))
        (Tuesday = Sunday))
        by (left; left; left; left; left; right; reflexivity).
    assert (Wed : or (or (or (or (or (or
        (Wednesday = Monday) (Wednesday = Tuesday))
        (Wednesday = Wednesday)) (Wednesday = Thursday))
        (Wednesday = Friday)) (Wednesday = Saturday))
        (Wednesday = Sunday))
        by (left; left; left; left; right; reflexivity).
    assert (Thu : or (or (or (or (or (or
        (Thursday = Monday) (Thursday = Tuesday))
        (Thursday = Wednesday)) (Thursday = Thursday))
        (Thursday = Friday)) (Thursday = Saturday))
        (Thursday = Sunday))
        by (left; left; left; right; reflexivity).
    assert (Fri : or (or (or (or (or (or
        (Friday = Monday) (Friday = Tuesday))
        (Friday = Wednesday)) (Friday = Thursday))
        (Friday = Friday)) (Friday = Saturday))
        (Friday = Sunday))
        by (left; left; right; reflexivity).
    assert (Sat : or (or (or (or (or (or
        (Saturday = Monday) (Saturday = Tuesday))
        (Saturday = Wednesday)) (Saturday = Thursday))
        (Saturday = Friday)) (Saturday = Saturday))
        (Saturday = Sunday))
        by (left; right; reflexivity).
    assert (Sun : or (or (or (or (or (or
        (Sunday = Monday) (Sunday = Tuesday))
        (Sunday = Wednesday)) (Sunday = Thursday))
        (Sunday = Friday)) (Sunday = Saturday))
        (Sunday = Sunday))
        by (right; reflexivity).
    exact (fun (d : Day_of_the_Week)
        => match d return or (or (or (or (or (or
            (d = Monday) (d = Tuesday))
            (d = Wednesday)) (d = Thursday))
            (d = Friday)) (d = Saturday))
            (d = Sunday)
        with Monday => Mon
        | Tuesday => Tue
        | Wednesday => Wed
        | Thursday => Thu
        | Friday => Fri
        | Saturday => Sat
        | Sunday => Sun
        end).
Qed.

(** The second assertion was that Day_before was
the inverse function of Day_after; that is,
Day_before (Day_after (d)) = d for any d.
We really should prove that: *)

Theorem Day_before_inverse_of_Day_after
    : forall d : Day_of_the_Week, Day_before (Day_after d) = d.
Proof.
    assert (D_b_D_a_Monday : Day_before (Day_after (Monday)) = Monday) by reflexivity.
    assert (D_b_D_a_Tuesday : Day_before (Day_after (Tuesday)) = Tuesday) by reflexivity.
    assert (D_b_D_a_Wednesday : Day_before (Day_after (Wednesday)) = Wednesday) by reflexivity.
    assert (D_b_D_a_Thursday : Day_before (Day_after (Thursday)) = Thursday) by reflexivity.
    assert (D_b_D_a_Friday : Day_before (Day_after (Friday)) = Friday) by reflexivity.
    assert (D_b_D_a_Saturday : Day_before (Day_after (Saturday)) = Saturday) by reflexivity.
    assert (D_b_D_a_Sunday : Day_before (Day_after (Sunday)) = Sunday) by reflexivity.
    exact (fun (d : Day_of_the_Week)
        => match d
        with Monday => D_b_D_a_Monday
        | Tuesday => D_b_D_a_Tuesday
        | Wednesday => D_b_D_a_Wednesday
        | Thursday => D_b_D_a_Thursday
        | Friday => D_b_D_a_Friday
        | Saturday => D_b_D_a_Saturday
        | Sunday => D_b_D_a_Sunday
        end).
Qed.

(** And that is it for simple types.
In the next article, I plan on tackling types that contain other types. *)

End Four.