Require Coq.QArith.QArith.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.BinIntDef.
Require Coq.Numbers.BinNums.

Module Quaternions.

    Import Coq.QArith.QArith.
    Import Coq.ZArith.ZArith.
    Import Coq.ZArith.BinIntDef.
    Import Coq.Numbers.BinNums.

    Inductive H : Set :=
        H_make (w x y z : Q) : H.

    Definition H_from (w : Q) :=
        H_make (w) (0) (0) (0).

    Definition H_zero := H_from (0).
    Definition H_one := H_from (1).
    Definition H_neg_one := H_from (-1).

    Definition i := H_make (0) (1) (0) (0).
    Definition j := H_make (0) (0) (1) (0).
    Definition k := H_make (0) (0) (0) (1).

    Definition Re (left : H) :=
        match (left) with H_make (w) (x) (y) (z) => w end.

    Definition Icoeff (left : H) :=
        match (left) with H_make (w) (x) (y) (z) => x end.

    Definition Jcoeff (left : H) :=
        match (left) with H_make (w) (x) (y) (z) => y end.

    Definition Kcoeff (left : H) :=
        match (left) with H_make (w) (x) (y) (z) => z end.

    Definition H_plus (left: H) (right : H) : H
        := match (left)
        with H_make (wl) (xl) (yl) (zl)
        => match (right)
        with H_make (wr) (xr) (yr) (zr)
        => H_make (wl + wr) (xl + xr) (yl + yr) (zl + zr)
        end end.

    Definition H_opp (right: H) : H
        := match (right) with H_make (wr) (xr) (yr) (zr)
        => H_make (- wr) (- xr) (- yr) (- zr) end.

    Definition H_conj (right: H) : H
        := match (right) with H_make (wr) (xr) (yr) (zr)
        => H_make (wr) (- xr) (- yr) (- zr) end.

    Definition H_norm_squared (right: H) : Q
        := match (right)
        with H_make (wr) (xr) (yr) (zr)
        => (wr * wr) + (xr * xr)
            + (yr * yr) + (zr * zr) end.

    Definition H_mul (left: H) (right : H) : H
        := match (left)
        with H_make (wl) (xl) (yl) (zl)
        => match (right)
        with H_make (wr) (xr) (yr) (zr)
        => H_make ((wl * wr) - (xl * xr)
                             - (yl * yr) - (zl * zr))
                  ((wl * xr) + (xl * wr)
                             + (yl * zr) - (zl * yr))
                  ((wl * yr) - (xl * zr)
                             + (yl * wr) + (zl * xr))
                  ((wl * zr) + (xl * yr)
                             - (yl * xr) + (zl * wr)) end end.

    Definition H_inv (left: H) : H
        := match (left)
        with H_make (0) (0) (0) (0) => H_zero
        | H_make (wl) (xl) (yl) (zl)
        =>  let den := wl * wl + xl * xl + yl * yl + zl * zl
            in H_make (wl / den) (- xl / den)
                (- yl / den) (- zl / den)
        end.

    Definition H_eq (left: H) (right: H) : Prop
        := match (left)
        with H_make (wl) (xl) (yl) (zl)
        => match (right)
        with H_make (wr) (xr) (yr) (zr)
        => (and (and (Qeq (wl) (wr))
                     (Qeq (xl) (xr)))
                (and (Qeq (yl) (yr))
                     (Qeq (zl) (zr)))) end end.

    Section Required_properties.

        Definition Q_zero_times_zero_equals_zero
            := Qmult_0_l (0).

        Definition Q_zero_times_one_equals_zero
            := Qmult_0_l (1).

        Definition Q_one_times_zero_equals_zero
            := Qmult_1_l (0).

        Definition Q_one_times_one_equals_one
            := Qmult_1_l (1).

        Lemma i_squared_equals_negative_one
            : H_eq (H_mul i i) (H_neg_one).
        Proof.
            unfold H_neg_one.
            unfold H_mul.
            unfold i.
            unfold H_from.
            unfold H_eq.
            unfold Qminus.

            assert (Lem1 :
                Qeq (Qopp (0*0)) (0)).
                unfold Qmult.
                unfold Qnum.
                unfold Qden.
                rewrite (Coq.PArith.BinPos.Pos.mul_1_l (1%positive)).
                rewrite (Z.mul_0_l (0)).
                unfold Qopp.
                unfold Qeq.
                unfold Qnum.
                unfold Qden.
                unfold Z.opp.
                reflexivity.


rewrite (P.mul_1_l (1)).
                unfold Qeq.

        assert (QXXXXX : Qeq (0 + - (1) + 0 + 0)
                             (0 + - (1) + 0))
            by exact (Qplus_0_r (0 + - (1) + 0)).


        assert (QXXXX : Qeq (0 + - (1) + 0)
                            (0 + - (1)))
         by exact (Qplus_0_r   (0 + - (1))).

        assert (QXXXXXX : Qeq (0 + - (1) + 0 + 0)
                              (0 + - (1)))
         by exact (Qeq_trans (0 + - (1) + 0 + 0)
                          (0 + - (1) + 0)
                          (0 + - (1))
                          (QXXXXX) (QXXXX)).

        assert (QY : eq ((0:Q) * (1:Q))
                     (0#1)) by reflexivity.

        assert (QYY : eq ((1:Q) * (0:Q))
                     (0#1)) by reflexivity.

        rewrite QY.
        rewrite QYY.

        assert (QYYY := Qplus_0_r (0 + 0 + 0)).
        assert (QYYYY := Qplus_0_r (0 + 0)).
        assert (QYYYYY := Qplus_0_r (0)).
        assert (QYYYYYY := Qeq_trans
                       (0+0+0+0) (0+0+0) (0+0)
                       (QYYY) (QYYYY)).

        assert (QYYYYYYY := Qeq_trans
                       (0+0+0+0) (0+0) (0)
                       (QYYYYYY) (QYYYYY)).

        assert (QZZ : Qeq (Qopp 0) (0))
           by reflexivity.

        pose (QZZZ := Qopp 0).

        assert (QZZZZ := Qplus_0_l (QZZZ)).
        assert (QZZZZZ := Qplus_0_r
               (0 + QZZZ)).
        assert (QZZZZZZ := Qplus_0_r
               (0 + QZZZ + 0)).

        assert (QZZZZZZZ := Qeq_trans
                (0 + QZZZ + 0 + 0)
                (0 + QZZZ + 0)
                (0 + QZZZ)
                (QZZZZZZ) (QZZZZZ)).

        assert (QZZZZZZZZ := Qeq_trans
                (0 + QZZZ + 0 + 0)
                (0 + QZZZ)
                (QZZZ) (QZZZZZZZ) (QZZZZ)).

        assert (QZZZZZZZZZ := Qeq_trans
                (0 + QZZZ + 0 + 0)
                (QZZZ)
                (0) (QZZZZZZZZ) (QZZ)).

        assert (QA := Qplus_0_r (0+0+-0)).
        assert (QAA := Qplus_assoc
                      (0) (0) (-0)).
        assert (QAAA := Qplus_0_l (0+-0)).
        assert (QAAAA := Qplus_0_l (-0)).
        assert (QAAAXA := Qeq_trans
                     (0 + - 0)
                     (- 0)
                     (0) (QAAAA) (QZZ)).
        assert (QAAAXAA := Qeq_trans
                     (0 + (0 + - 0))
                     (0 + - 0)
                     (0) (QAAA) QAAAXA).
        assert (QAAAXAAA := Qeq_sym
                    (0 + (0 + - 0))
                    (0 + 0 + - 0) (QAA )    ).
        assert (QAAAXAAAX := Qeq_trans
                    (0 + 0 + - 0)
                    (0 + (0 + - 0))
                    (0)
                    (QAAAXAAA) (QAAAXAA)).
        assert (QAAAXAAAXA := Qeq_trans
                    (0 + 0 + - 0 + 0)
                    (0 + 0 + - 0)
                    (0)
                    (QA) (QAAAXAAAX)).
        assert (QB := conj (QXXXXXX)
                           (QYYYYYYY)).
        assert (QC := conj (QZZZZZZZZZ)
                           (QAAAXAAAXA)).
        assert (QD := conj (QB) (QC)).
        exact QD.
Qed.

    Theorem Add_is_commutative :
        forall (left : H) (right : H),
        H_eq (H_plus left right) (H_plus right left).

    Proof.
        intro left.
        destruct left as [w_left x_left y_left z_left].
        intro right.
        destruct right as [w_right x_right y_right z_right].
        unfold H_plus.
        unfold H_eq.

        assert (QA := Qplus_comm
                  w_left  w_right).
        assert (QB := Qplus_comm
                  x_left  x_right).
        assert (QC := Qplus_comm
                  y_left  y_right).
        assert (QD := Qplus_comm
                  z_left  z_right).
        assert (QE := conj(conj QA QB)(conj QC QD)).
        exact QE.
    Qed.
(*
    Theorem Add_is_associative:
        forall (left: H) (middle: H) (right: H),
        eq (Add left (Add middle right))
           (Add (Add left middle) right).
    Proof.
        intro left.
        destruct left as [w_left x_left y_left z_left].
        intro middle.
        destruct middle as [w_middle x_middle y_middle z_middle].
        intro right.
        destruct right as [w_right x_right y_right z_right].
        unfold Add.
        unfold Re.
        unfold Icoeff.
        unfold Jcoeff.
        unfold Kcoeff.
        rewrite (Reals.Add_is_associative (w_left) (w_middle) (w_right)).
        rewrite (Reals.Add_is_associative (x_left) (x_middle) (x_right)).
        rewrite (Reals.Add_is_associative (y_left) (y_middle) (y_right)).
        rewrite (Reals.Add_is_associative (z_left) (z_middle) (z_right)).
        reflexivity.
    Qed.

    Theorem Add_identity_is_zero:
        forall (right: H), eq (Add zero right) (right).
    Proof.
        intro right.
        destruct right as [w_right x_right y_right z_right].
        unfold Add.
        unfold zero.
        unfold Re.
        unfold Icoeff.
        unfold Jcoeff.
        unfold Kcoeff.
        rewrite (Reals.Add_identity_is_zero (w_right)).
        rewrite (Reals.Add_identity_is_zero (x_right)).
        rewrite (Reals.Add_identity_is_zero (y_right)).
        rewrite (Reals.Add_identity_is_zero (z_right)).
        reflexivity.
    Qed.

    Axiom Zero_is_add_identity:
        forall (left: H), eq (Add left zero) (left).

    Axiom Add_real_to_Neg_real:
        forall (x : H), eq (Add (x) (Neg x)) (zero).

    Axiom Add_Neg_real_to_real:
        forall (x : H), eq (Add (Neg x) (x)) (zero).

    Axiom Zero_is_Neg_zero: eq (zero) (Neg zero).

    Axiom Neg_zero_is_zero: eq (Neg zero) (zero).

    Axiom Mul_unique_left:
        forall (left1: H) (left2: H) (right: H)
        (sums_are_equal : eq (Mul left1 right) (Mul left2 right)),
        eq left1 left2.

    Axiom Mul_unique_right:
        forall (left: H) (right1: H) (right2: H)
        (sums_are_equal : eq (Mul left right1) (Mul left right2)),
        eq right1 right2.

    Axiom Mul_unique_product:
        forall (left: H) (right: H) (product1: H) (product2: H)
        (eq1: eq (Mul left right) product1)
        (eq2: eq (Mul left right) product2),
        eq product1 product2.

    Axiom Mul_is_commutative:
        forall (left: H) (right: H),
        eq (Mul left right) (Mul right left).

    Axiom Mul_is_associative:
        forall (left: H) (middle: H) (right: H),
        eq (Mul (left) (Mul middle right))
           (Mul (Mul left middle) (right)).

    Axiom Mul_is_distributive_left:
        forall (left: H) (middle: H) (right: H),
        eq (Mul (Add left middle) (right))
           (Add (Mul left right) (Mul middle right)).

    Axiom Mul_is_distributive_right:
        forall (left: H) (middle: H) (right: H),
        eq (Mul (left) (Add middle right))
           (Add (Mul left middle) (Mul left right)).

    Axiom Mul_identity_is_zero:
        forall (right: H), eq (Mul one right) (right).

    Axiom One_is_Mul_identity:
        forall (left: H), eq (Mul left one) (left).

    Axiom Mul_real_by_Inv_real:
        forall (left: H) (not_zero : not (eq left zero)),
        eq (Mul (left) (Inv left not_zero)) (one).

    Axiom Mul_Inv_real_by_real:
        forall (right: H) (not_zero : not (eq right zero)),
        eq (Mul (Inv right not_zero) (right)) (one).
*)

    End Required_properties.

End Quaternions.

Print Quaternions.H.

Print QArith_base.Qopp.


