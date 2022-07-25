Add LoadPath "C:\Users\darre\Coq_sessions\Articles" as Darren's.Articles.
Load Article_5_Types_in_other_types.

Module Article_6_Lists_of_things.

    Module First_try.

    Inductive List_of_dates : Set :=
        make_list (first : Date) (second : Date) (third : Date).

    Definition Home_County_2022 :=
        make_list (make_date (Friday) (July) (fifteenth) (Year2022))
            (make_date (Saturday) (July) (sixteenth) (Year2022))
            (make_date (Sunday) (July) (seventeenth) (Year2022)).

    Fail Definition SunFest_2022 :=
        make_list (make_date (Thursday) (July) (seventh) (Year2022))
            (make_date (Friday) (July) (eighth) (Year2022))
            (make_date (Saturday) (July) (ninth) (Year2022))
            (make_date (Sunday) (July) (tenth) (Year2022)).

    Fail Definition London_RibFest_2022 :=
        make_list (make_date (Thursday) (July) (twenty_eighth) (Year2022))
            (make_date (Friday) (July) (twenty_ninth) (Year2022))
            (make_date (Saturday) (July) (thirtieth) (Year2022))
            (make_date (Sunday) (July) (thirty_first) (Year2022))
            (make_date (Monday) (August) (first) (Year2022)).

    End First_try.

    Module Second_try.

    Fail Inductive List_of_dates : Set :=
        make_list (first : Date) (second : Date) (third : Date)
        | make_list (first : Date)
            (second : Date) (third : Date) (fourth : Date)
        | make_list (first : Date) (second : Date)
            (third : Date) (fourth : Date) (fifth : Date).

    Inductive List_of_dates : Set :=
        make_list (first : Date) (second : Date) (third : Date)
        | make_list' (first : Date)
            (second : Date) (third : Date) (fourth : Date)
        | make_list'' (first : Date) (second : Date)
            (third : Date) (fourth : Date) (fifth : Date).

    Definition Home_County_2022 :=
        make_list (make_date (Friday) (July) (fifteenth) (Year2022))
            (make_date (Saturday) (July) (sixteenth) (Year2022))
            (make_date (Sunday) (July) (seventeenth) (Year2022)).

    Definition SunFest_2022 :=
        make_list' (make_date (Thursday) (July) (seventh) (Year2022))
            (make_date (Friday) (July) (eighth) (Year2022))
            (make_date (Saturday) (July) (ninth) (Year2022))
            (make_date (Sunday) (July) (tenth) (Year2022)).

    Definition London_RibFest_2022 :=
        make_list'' (make_date (Thursday) (July) (twenty_eighth) (Year2022))
            (make_date (Friday) (July) (twenty_ninth) (Year2022))
            (make_date (Saturday) (July) (thirtieth) (Year2022))
            (make_date (Sunday) (July) (thirty_first) (Year2022))
            (make_date (Monday) (August) (first) (Year2022)).

    End Second_try.

    Module Third_try.

    Inductive List_of_dates : Set :=
        cons (head : Date) (tail : Date)
        | cons' (head : List_of_dates) (tail : Date).

    Definition Home_County_2022 :=
        cons' (cons (make_date (Friday) (July) (fifteenth) (Year2022))
                (make_date (Saturday) (July) (sixteenth) (Year2022)))
            (make_date (Sunday) (July) (seventeenth) (Year2022)).

    Definition SunFest_2022 :=
        cons' (cons' (cons (make_date (Thursday) (July) (seventh) (Year2022))
                    (make_date (Friday) (July) (eighth) (Year2022)))
                (make_date (Saturday) (July) (ninth) (Year2022)))
            (make_date (Sunday) (July) (tenth) (Year2022)).

    Definition London_RibFest_2022 :=
        cons' (cons' (cons' (cons
                        (make_date (Thursday) (July) (twenty_eighth) (Year2022))
                        (make_date (Friday) (July) (twenty_ninth) (Year2022)))
                    (make_date (Saturday) (July) (thirtieth) (Year2022)))
                (make_date (Sunday) (July) (thirty_first) (Year2022)))
            (make_date (Monday) (August) (first) (Year2022)).

    End Third_try.

    Module Fourth_try.

    Inductive List_of_dates : Set :=
        cons (head: Date) (tail : List_of_dates)
        | cons' (head : Date) (tail : Date).

    Definition Home_County_2022 :=
        cons (make_date (Friday) (July) (fifteenth) (Year2022))
             (cons' (make_date (Saturday) (July) (sixteenth) (Year2022))
                    (make_date (Sunday) (July) (seventeenth) (Year2022))).

    Definition SunFest_2022 :=
        cons (make_date (Thursday) (July) (seventh) (Year2022))
             (cons (make_date (Friday) (July) (eighth) (Year2022))
                   (cons' (make_date (Saturday) (July) (ninth) (Year2022))
                          (make_date (Sunday) (July) (tenth) (Year2022)))).

    Definition London_RibFest_2022 :=
        cons (make_date (Thursday) (July) (twenty_eighth) (Year2022))
            (cons (make_date (Friday) (July) (twenty_ninth) (Year2022))
                 (cons (make_date (Saturday) (July) (thirtieth) (Year2022))
                      (cons' (make_date (Sunday) (July) (thirty_first) (Year2022))
                          (make_date (Monday) (August) (first) (Year2022))))).

    End Fourth_try.

End Article_6_Lists_of_things.

