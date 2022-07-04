(** Article 5. Types inside other types. *)

(**

"This year our Australasian members
and the various organizations affiliated
to our Australasian branches put no fewer
than twenty-two things on top of other things."
-- Sir William [1]

This article is about making types
whose values are composed of values from
other types.  That is a confusing sentence,
so let us tackle it using familiar ideas.
We did this in the last article with the
calendar, and we shall also use the calendar
here.

Suppose that we need to represent a date
on the calendar.  To write a date in English,
one could write the day of the week,
the month of the year,
the day of the month (as an ordinal number,
from first to thirty-first), and the year.
We can imitate this in Coq like so:

*)

Fail Definition First_day_of_2000 : Date :=
    make_date (Saturday) (January) (first) (Year2000).

Fail Definition Northeast_blackout_of_2003 :=
    make_date (Thursday) (August) (fourteenth) (Year2003).

(**
Unlike the constructors for the days
of the week and the months of the year that
we defined last time, the constructor make_date
has four parameters.  To use make_date,
therefore, we need four arguments.
Once we put in the fourth argument,
we have a value of the Date type.

Of course, we cannot use these definitions
yet because we have not even defined the
Date type and the make_date constructor.
That definition will look like this:
*)

Fail Inductive Date : Set :=
    make_date (day_of_the_week : Day_of_the_Week)
       (month : Month_of_the_Year)
       (day_of_the_month : Day_of_the_Month)
       (year : Year).

(**
The only problem now is that we have not
defined Day_of_the_Week, Month_of_the_Year,
Day_of_the_Month, and Year.  We have to
define these types first.

Let us copy the Day_of_the_Week and
Month_of_the_Year types from the
previous article:
*)

Inductive Day_of_the_Week : Set :=
    Monday | Tuesday
    | Wednesday | Thursday
    | Friday | Saturday | Sunday.

Inductive Month_of_the_Year : Set :=
    January | February | March
    | April | May | June | July
    | August | September
    | October | November | December.

(**
Next, we define the Day_of_the_Month
and Year types:
*)

Inductive Day_of_the_Month : Set :=
    first | second | third | fourth
    | fifth | sixth | seventh | eighth
    | ninth | tenth | eleventh | twelfth
    | thirteenth | fourteenth | fifteenth
    | sixteenth | seventeenth | eighteenth
    | nineteenth | twentieth | twenty_first
    | twenty_second | twenty_third
    | twenty_fourth | twenty_fifth
    | twenty_sixth | twenty_seventh
    | twenty_eighth | twenty_ninth
    | thirtieth | thirty_first.

Inductive Year : Set :=
    Year2000 | Year2001 | Year2002 | Year2003
    | Year2004 | Year2005 | Year2006 | Year2007
    | Year2008 | Year2009 | Year2010 | Year2011
    | Year2012 | Year2013 | Year2014 | Year2015
    | Year2016 | Year2017 | Year2018 | Year2019
    | Year2020 | Year2021 | Year2022 | Year2023
    | Year2024 | Year2025 | Year2026 | Year2027
    | Year2028 | Year2029 | Year2030 | Year2031
    | Year2032 | Year2033 | Year2034 | Year2035
    | Year2036 | Year2037 | Year2038 | Year2039
    | Year2040 | Year2041 | Year2042 | Year2043
    | Year2044 | Year2045 | Year2046 | Year2047
    | Year2048 | Year2049 | Year2050 | Year2051
    | Year2052 | Year2053 | Year2054 | Year2055
    | Year2056 | Year2057 | Year2058 | Year2059
    | Year2060 | Year2061 | Year2062 | Year2063
    | Year2064 | Year2065 | Year2066 | Year2067
    | Year2068 | Year2069 | Year2070 | Year2071
    | Year2072 | Year2073 | Year2074 | Year2075
    | Year2076 | Year2077 | Year2078 | Year2079
    | Year2080 | Year2081 | Year2082 | Year2083
    | Year2084 | Year2085 | Year2086 | Year2087
    | Year2088 | Year2089 | Year2090 | Year2091
    | Year2092 | Year2093 | Year2094 | Year2095
    | Year2096 | Year2097 | Year2098 | Year2099.

(**
Now we can define the Date type.
*)

Inductive Date : Set :=
    make_date (day_of_the_week : Day_of_the_Week)
       (month : Month_of_the_Year)
       (day_of_the_month : Day_of_the_Month)
       (year : Year).

(** And now we can define those dates
that we couldn't define earlier: *)

Definition First_day_of_2000 : Date :=
    make_date (Saturday) (January) (first) (Year2000).

Definition Northeast_blackout_of_2003 :=
    make_date Thursday August fourteenth Year2003.

Inductive Date2 : Set :=
    make_date2 : forall day_of_the_week : Day_of_the_Week,
        forall month : Month_of_the_Year,
        forall day_of_the_month : Day_of_the_Month,
        forall year : Year, Date2.

(*
Definition Date_after (the_date : Date) :=
    match the_date
    with Make_Date (_ as day_w) (December) (thirty_first) (Year2099)
=> Make_Date (day_w) (December) (thirty_first) (Year2099)
|    Make_Date (_ as day_w) (_ as month) (_ as day_m) (_ as year)
=> Make_Date (Day_after(day_w))(month)(Day_of_Month_after(day_m))(year)
end.
*)

(** [1] Chapman, Graham, and John Cleese
    and Terry Gilliam and Eric Idle
    and Terry Jones and Michael Palin.
    "The Royal Society for
    Putting Things On Top Of Other Things."
    Sketch in episode 18 of
    "Monty Python's Flying Circus."
    BBC, 1970.  Quoted in
    "Monty Python's Flying Circus:
    Just the Words."  Methuen, 1989.
    Graham Chapman portrays Sir William. *)
