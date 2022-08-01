(** Article 5. Types inside other types. *)

(**

"This year our Australasian members
and the various organizations affiliated
to our Australasian branches put no fewer
than twenty-two things on top of other things."
-- Sir William [1]

This article is about making types
whose values are composed of values from
other types.  That topic sounds complex,
so let us tackle it using familiar ideas.

*)

Module Article_5_Types_in_other_types.

(**

We did this in the last article with the
calendar, and we shall also use the calendar
here:

*)

Inductive Day_of_the_Week : Set :=
    Monday | Tuesday
    | Wednesday | Thursday
    | Friday | Saturday | Sunday.

Definition Day_after (d : Day_of_the_Week) :=
    match d return Day_of_the_Week
    with Monday => Tuesday
    | Tuesday => Wednesday
    | Wednesday => Thursday
    | Thursday => Friday
    | Friday => Saturday
    | Saturday => Sunday
    | Sunday => Monday
    end.

Inductive Month_of_the_Year : Set :=
    January | February | March
    | April | May | June | July
    | August | September
    | October | November | December.

Definition Month_after (m : Month_of_the_Year) :=
    match m return Month_of_the_Year
    with January => February
    | February => March
    | March => April
    | April => May
    | May => June
    | June => July
    | July => August
    | August => September
    | September => October
    | October => November
    | November => December
    | December => January
    end.

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

Definition Day_of_Month_after (d : Day_of_the_Month) :=
    match d return Day_of_the_Month
    with first => second
    | second => third
    | third => fourth
    | fourth => fifth
    | fifth => sixth
    | sixth => seventh
    | seventh => eighth
    | eighth => ninth
    | ninth => tenth
    | tenth => eleventh
    | eleventh => twelfth
    | twelfth => thirteenth
    | thirteenth => fourteenth
    | fourteenth => fifteenth
    | fifteenth => sixteenth
    | sixteenth => seventeenth
    | seventeenth => eighteenth
    | eighteenth => nineteenth
    | nineteenth => twentieth
    | twentieth => twenty_first
    | twenty_first => twenty_second
    | twenty_second => twenty_third
    | twenty_third => twenty_fourth
    | twenty_fourth => twenty_fifth
    | twenty_fifth => twenty_sixth
    | twenty_sixth => twenty_seventh
    | twenty_seventh => twenty_eighth
    | twenty_eighth => twenty_ninth
    | twenty_ninth => thirtieth
    | thirtieth => thirty_first
    | thirty_first => first
    end.

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

Definition Year_after (y : Year) :=
    match y
    with Year2000 => Year2001 | Year2050 => Year2051
    |    Year2001 => Year2002 | Year2051 => Year2052
    |    Year2002 => Year2003 | Year2052 => Year2053
    |    Year2003 => Year2004 | Year2053 => Year2054
    |    Year2004 => Year2005 | Year2054 => Year2055
    |    Year2005 => Year2006 | Year2055 => Year2056
    |    Year2006 => Year2007 | Year2056 => Year2057
    |    Year2007 => Year2008 | Year2057 => Year2058
    |    Year2008 => Year2009 | Year2058 => Year2059
    |    Year2009 => Year2010 | Year2059 => Year2060
    |    Year2010 => Year2011 | Year2060 => Year2061
    |    Year2011 => Year2012 | Year2061 => Year2062
    |    Year2012 => Year2013 | Year2062 => Year2063
    |    Year2013 => Year2014 | Year2063 => Year2064
    |    Year2014 => Year2015 | Year2064 => Year2065
    |    Year2015 => Year2016 | Year2065 => Year2066
    |    Year2016 => Year2017 | Year2066 => Year2067
    |    Year2017 => Year2018 | Year2067 => Year2068
    |    Year2018 => Year2019 | Year2068 => Year2069
    |    Year2019 => Year2020 | Year2069 => Year2070
    |    Year2020 => Year2021 | Year2070 => Year2071
    |    Year2021 => Year2022 | Year2071 => Year2072
    |    Year2022 => Year2023 | Year2072 => Year2073
    |    Year2023 => Year2024 | Year2073 => Year2074
    |    Year2024 => Year2025 | Year2074 => Year2075
    |    Year2025 => Year2026 | Year2075 => Year2076
    |    Year2026 => Year2027 | Year2076 => Year2077
    |    Year2027 => Year2028 | Year2077 => Year2078
    |    Year2028 => Year2029 | Year2078 => Year2079
    |    Year2029 => Year2030 | Year2079 => Year2080
    |    Year2030 => Year2031 | Year2080 => Year2081
    |    Year2031 => Year2032 | Year2081 => Year2082
    |    Year2032 => Year2033 | Year2082 => Year2083
    |    Year2033 => Year2034 | Year2083 => Year2084
    |    Year2034 => Year2035 | Year2084 => Year2085
    |    Year2035 => Year2036 | Year2085 => Year2086
    |    Year2036 => Year2037 | Year2086 => Year2087
    |    Year2037 => Year2038 | Year2087 => Year2088
    |    Year2038 => Year2039 | Year2088 => Year2089
    |    Year2039 => Year2040 | Year2089 => Year2090
    |    Year2040 => Year2041 | Year2090 => Year2091
    |    Year2041 => Year2042 | Year2091 => Year2092
    |    Year2042 => Year2043 | Year2092 => Year2093
    |    Year2043 => Year2044 | Year2093 => Year2094
    |    Year2044 => Year2045 | Year2094 => Year2095
    |    Year2045 => Year2046 | Year2095 => Year2096
    |    Year2046 => Year2047 | Year2096 => Year2097
    |    Year2047 => Year2048 | Year2097 => Year2098
    |    Year2048 => Year2049 | Year2098 => Year2099
    |    Year2049 => Year2050 | Year2099 => Year2099
    end.

Inductive Date : Set :=
    Make_Date (day_w : Day_of_the_Week)
       (month : Month_of_the_Year)
       (day_m : Day_of_the_Month)
       (y : Year).

Definition Date_after (the_date : Date) :=
    match the_date
    with Make_Date (_ as day_w) (December) (thirty_first) (Year2099) => Make_Date (day_w) (December) (thirty_first) (Year2099)
    |    Make_Date (_ as day_w) (_ as month) (_ as day_m) (_ as year) => Make_Date (Day_after (day_w)) (month) (Day_of_Month_after (day_m)) (year)
end.

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

End Article_5_Types_in_other_types.
