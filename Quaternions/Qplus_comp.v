Require Import Coq.QArith.QArith.

Module Qplus_comp_derivations.

    Definition Qzero  : Q := 0.
    Definition Qone   : Q := 1.
    Definition Qtwo   : Q := 2.
    Definition Qthree : Q := 3.
    Definition Qfour  : Q := 4.
    Definition Qfive  : Q := 5.
    Definition Qsix   : Q := 6.
    Definition Qseven : Q := 7.
    Definition Qeight : Q := 8.

    Definition Qone_minus_one
        := Qminus (Qone) (Qone).

    Definition Qplus_derivation_one
        : (Qeq (Qone_minus_one) (Qzero))
            -> ((Qeq ==> Qeq)%signature)
            (Qplus (Qone_minus_one))
            (Qplus (Qzero))
        := Qplus_comp
            (Qone_minus_one) (Qzero).

    Definition Qone_minus_one_is_zero
        : Qeq (Qone_minus_one) (Qzero)
        := eq_refl.

    Definition Qplus_derivation_two
        : ((Qeq ==> Qeq)%signature)
            (Qplus (Qone_minus_one))
            (Qplus (Qzero))
        := Qplus_comp
            (Qone_minus_one) (Qzero)
            (Qone_minus_one_is_zero).

    Definition Qeight_minus_two : Q
        := Qminus (Qeight) (Qtwo).

    Definition Qeight_minus_two_equals_six
        : Qeq (Qeight_minus_two) (Qsix)
        := eq_refl.

    Definition Qplus_derivation_three
        : (Qeight_minus_two == Qsix)
            -> (Qone_minus_one + Qeight_minus_two 
                == Qzero + Qsix)
        := Qplus_comp
            (Qone_minus_one) (Qzero)
            (Qone_minus_one_is_zero)
            (Qeight_minus_two) (Qsix).

    Definition Qplus_derivation_four
        : (Qone_minus_one + Qeight_minus_two
            == Qzero + Qsix)
        := Qplus_comp
            (Qone_minus_one) (Qzero)
            (Qone_minus_one_is_zero)
            (Qeight_minus_two) (Qsix)
            (Qeight_minus_two_equals_six).

    Definition Qopp_derivation_one
        : forall x : Q,
            forall y : Q,
            forall x_Qeq_y : Qeq (x) (y),
            Qeq (Qopp (x)) (Qopp (y))
        := Qopp_comp.

End Qplus_comp_derivations.
