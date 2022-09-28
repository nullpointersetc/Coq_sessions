Require Coq.QArith.QArith.

Module Quaternions.

    Import Coq.QArith.QArith.

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
            : Qeq (Qmult (0%Q) (0%Q)) (0%Q)
            := Qmult_0_l (0%Q).

        Definition Q_zero_equals_zero_times_zero
            : Qeq (0%Q) (Qmult (0%Q) (0%Q))
            := Qeq_sym (Qmult (0%Q) (0%Q))
                (0%Q)
                (Q_zero_times_zero_equals_zero).

        Definition Q_zero_times_one_equals_zero
            : Qeq (Qmult (0%Q) (1%Q)) (0%Q)
            := Qmult_0_l (1%Q).

        Definition Q_zero_equals_zero_times_one
            : Qeq (0%Q) (Qmult (0%Q) (1%Q))
            := Qeq_sym (Qmult (0%Q) (1%Q))
                (0%Q)
                (Q_zero_times_one_equals_zero).

        Definition Q_one_times_zero_equals_zero
            : Qeq (Qmult (1%Q) (0%Q)) (0%Q)
            := Qmult_1_l (0%Q).

        Definition Q_zero_equals_one_times_zero
            : Qeq (0%Q) (Qmult (1%Q) (0%Q))
            := Qeq_sym (Qmult (1%Q) (0%Q))
                (0%Q)
                (Q_one_times_zero_equals_zero).

        Definition Q_one_times_one_equals_one
            : Qeq (Qmult (1%Q) (1%Q)) (1%Q)
            := Qmult_1_l (1%Q).

        Definition Q_one_equals_one_times_one
            : Qeq (1%Q) (Qmult (1%Q) (1%Q))
            := Qeq_sym (Qmult (1%Q) (1%Q))
                (1%Q)
                (Q_one_times_one_equals_one).

        Lemma i_squared_equals_negative_one
            : H_eq (H_mul i i) (H_neg_one).
        Proof.
            assert (Real_part := eq_refl
                : 0*0 - 1*1 - 0*0 - 0*0 == -1).

            assert (I_coeff_part := eq_refl
                : 0*1 + 1*0 + 0*0 - 0*0 == 0).

            assert (J_coeff_part := eq_refl
                : 0*0 - 1*0 + 0*0 + 0*1 == 0).

            assert (K_coeff_part := eq_refl
                : 0*0 + 1*0 - 0*1 + 0*1 == 0).

            exact (conj (conj (Real_part)
                              (I_coeff_part))
                        (conj (J_coeff_part)
                              (K_coeff_part))).
        Qed.

        Theorem Add_is_commutative :
            forall (left : H) (right : H),
            H_eq (H_plus left right)
                 (H_plus right left).
        Proof.
            intro left.
            destruct left as [w_left x_left y_left z_left].
            intro right.
            destruct right as [w_right x_right y_right z_right].

            exact (conj (conj (Qplus_comm (w_left) (w_right))
                              (Qplus_comm (x_left) (x_right)))
                        (conj (Qplus_comm (y_left) (y_right))
                              (Qplus_comm (z_left) (z_right)))).
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

