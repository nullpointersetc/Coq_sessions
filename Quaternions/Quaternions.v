Module Reals.
    Axiom R : Set.
    Axiom zero : R.
    Axiom one : R.

    Axiom Add : forall left: R,
                forall right: R, R.

    Axiom Add_is_commutative:
        forall left: R,
        forall right: R,
        eq (Add left right) (Add right left).

    Axiom Add_is_associative:
        forall left: R,
        forall middle: R,
        forall right: R,
        eq (Add left (Add middle right))
           (Add (Add left middle) right).

    Axiom Additive_identity_is_zero:
        forall left: R,
        eq (Add left zero) (left).

    Axiom Neg : forall left: R, R.

    Axiom Add_real_to_Neg_real :
        forall x : R,
        eq (Add (x) (Neg x)) (zero).

    Axiom Mul : forall left: R,
                forall right: R, R.

    Axiom Mul_is_commutative :
        forall left : R, forall right : R,
        eq (Mul left right) (Mul right left).

    Axiom Mul_is_associative :
        forall left : R, forall middle : R,
        forall right : R,
        eq (Mul (left) (Mul middle right))
           (Mul (Mul left middle) (right)).

    Axiom Mul_is_distributive_first :
        forall left : R, forall middle : R,
        forall right : R,
        eq (Mul (Add left middle) (right))
           (Add (Mul left right)
                (Mul middle right)).

    Axiom Mul_is_distributive_second :
        forall left : R, forall middle : R,
        forall right : R,
        eq (Mul (left) (Add middle right))
           (Add (Mul left middle)
                (Mul left right)).

    Axiom Mul_identity_is_one :
        forall left : R,
        eq (Mul (one) (left)) (left).

    Axiom Inv :
        forall left : R,
        forall not_zero : not (eq left zero), R.

    Axiom Mul_real_by_Inv_real :
        forall left : R,
        forall not_zero : not (eq left zero),
        eq (Mul (left) (Inv left not_zero))
           (one).


End Reals.

Module Quaternions.

    Inductive H : Set :=
        New (w : Reals.R) (x : Reals.R)
             (y : Reals.R) (z : Reals.R) : H.

    Definition zero :=
        New (Reals.zero) (Reals.zero)
            (Reals.zero) (Reals.zero).

    Definition one :=
        New (Reals.one) (Reals.zero)
            (Reals.zero) (Reals.zero).

    Definition i :=
        New (Reals.zero) (Reals.one)
            (Reals.zero) (Reals.zero).

    Definition j :=
        New (Reals.zero) (Reals.zero)
            (Reals.one) (Reals.zero).

    Definition k :=
        New (Reals.zero) (Reals.zero)
            (Reals.zero) (Reals.one).

    Definition Re (left: H) : Reals.R
        := match (left)
        with New (w) (x) (y) (z) => w
        end.

    Definition Icoeff (left: H) : Reals.R
        := match (left)
        with New (w) (x) (y) (z) => x
        end.

    Definition Jcoeff (left: H) : Reals.R
        := match (left)
        with New (w) (x) (y) (z) => y
        end.

    Definition Kcoeff (left: H) : Reals.R
        := match (left)
        with New (w) (x) (y) (z) => z
        end.

    Definition Add (left: H) (right : H) : H
        := New (Reals.Add (Re left) (Re right))
            (Reals.Add (Icoeff left) (Icoeff right))
            (Reals.Add (Jcoeff left) (Jcoeff right))
            (Reals.Add (Kcoeff left) (Kcoeff right)).

    Theorem Add_is_commutative :
        forall left : H, forall right : H,
        eq (Add left right) (Add right left).

    Proof.
        intro left.
        intro right.
        unfold Add.

        rewrite (Reals.Add_is_commutative
            (Re left) (Re right)).

        rewrite (Reals.Add_is_commutative
            (Icoeff left) (Icoeff right)).

        rewrite (Reals.Add_is_commutative
            (Jcoeff left) (Jcoeff right)).

        rewrite (Reals.Add_is_commutative
            (Kcoeff left) (Kcoeff right)).

        reflexivity.
    Qed.

End Quaternions.
