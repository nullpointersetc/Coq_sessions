Module Reals.
    Axiom Real : Set.
    Axiom zero : Real.
    Axiom one : Real.

    Axiom Add : forall (left: Real) (right: Real), Real.

    Axiom Add_unique_left:
        forall (left1: Real) (left2: Real) (right: Real)
        (sums_are_equal : eq (Add left1 right) (Add left2 right)),
        eq left1 left2.

    Axiom Add_unique_right:
        forall (left: Real) (right1: Real) (right2: Real)
        (sums_are_equal : eq (Add left right1) (Add left right2)),
        eq right1 right2.

    Axiom Add_unique_sum:
        forall (left: Real) (right: Real) (sum1: Real) (sum2: Real)
        (eq1: eq (Add left right) sum1)
        (eq2: eq (Add left right) sum2),
        eq sum1 sum2.

    Axiom Add_is_commutative:
        forall (left: Real) (right: Real),
        eq (Add left right) (Add right left).

    Axiom Add_is_associative:
        forall (left: Real) (middle: Real) (right: Real),
        eq (Add left (Add middle right))
           (Add (Add left middle) right).

    Axiom Add_identity_is_zero:
        forall (right: Real), eq (Add zero right) (right).

    Axiom Zero_is_add_identity:
        forall (left: Real), eq (Add left zero) (left).

    Axiom Neg: forall (left: Real), Real.

    Axiom Add_real_to_Neg_real:
        forall (x : Real), eq (Add (x) (Neg x)) (zero).

    Axiom Add_Neg_real_to_real:
        forall (x : Real), eq (Add (Neg x) (x)) (zero).

    Axiom Zero_is_Neg_zero: eq (zero) (Neg zero).

    Axiom Neg_zero_is_zero: eq (Neg zero) (zero).

    Axiom Mul: forall (left: Real) (right: Real), Real.

    Axiom Mul_unique_left:
        forall (left1: Real) (left2: Real) (right: Real)
        (sums_are_equal : eq (Mul left1 right) (Mul left2 right)),
        eq left1 left2.

    Axiom Mul_unique_right:
        forall (left: Real) (right1: Real) (right2: Real)
        (sums_are_equal : eq (Mul left right1) (Mul left right2)),
        eq right1 right2.

    Axiom Mul_unique_product:
        forall (left: Real) (right: Real) (product1: Real) (product2: Real)
        (eq1: eq (Mul left right) product1)
        (eq2: eq (Mul left right) product2),
        eq product1 product2.

    Axiom Mul_is_commutative:
        forall (left: Real) (right: Real),
        eq (Mul left right) (Mul right left).

    Axiom Mul_is_associative:
        forall (left: Real) (middle: Real) (right: Real),
        eq (Mul (left) (Mul middle right))
           (Mul (Mul left middle) (right)).

    Axiom Mul_is_distributive_left:
        forall (left: Real) (middle: Real) (right: Real),
        eq (Mul (Add left middle) (right))
           (Add (Mul left right) (Mul middle right)).

    Axiom Mul_is_distributive_right:
        forall (left: Real) (middle: Real) (right: Real),
        eq (Mul (left) (Add middle right))
           (Add (Mul left middle) (Mul left right)).

    Axiom Mul_identity_is_zero:
        forall (right: Real), eq (Mul one right) (right).

    Axiom One_is_Mul_identity:
        forall (left: Real), eq (Mul left one) (left).

    Axiom Inv:
        forall (left: Real) (not_zero : not (eq left zero)), Real.

    Axiom Mul_real_by_Inv_real:
        forall (left: Real) (not_zero : not (eq left zero)),
        eq (Mul (left) (Inv left not_zero)) (one).

    Axiom Mul_Inv_real_by_real:
        forall (right: Real) (not_zero : not (eq right zero)),
        eq (Mul (Inv right not_zero) (right)) (one).

End Reals.

Module Quaternions.

    Inductive Hamilton : Set :=
        Quaternion (w : Reals.Real) (x : Reals.Real)
             (y : Reals.Real) (z : Reals.Real) : Hamilton.

    Definition zero :=
        Quaternion (Reals.zero) (Reals.zero)
            (Reals.zero) (Reals.zero).

    Definition one :=
        Quaternion (Reals.one) (Reals.zero)
            (Reals.zero) (Reals.zero).

    Definition i :=
        Quaternion (Reals.zero) (Reals.one)
            (Reals.zero) (Reals.zero).

    Definition j :=
        Quaternion (Reals.zero) (Reals.zero)
            (Reals.one) (Reals.zero).

    Definition k :=
        Quaternion (Reals.zero) (Reals.zero)
            (Reals.zero) (Reals.one).

    Definition Re (left: Hamilton) : Reals.Real
        := match (left)
        with Quaternion (w) (x) (y) (z) => w
        end.

    Definition Icoeff (left: Hamilton) : Reals.Real
        := match (left)
        with Quaternion (w) (x) (y) (z) => x
        end.

    Definition Jcoeff (left: Hamilton) : Reals.Real
        := match (left)
        with Quaternion (w) (x) (y) (z) => y
        end.

    Definition Kcoeff (left: Hamilton) : Reals.Real
        := match (left)
        with Quaternion (w) (x) (y) (z) => z
        end.

    Definition Add (left: Hamilton) (right : Hamilton) : Hamilton
        := Quaternion (Reals.Add (Re left) (Re right))
            (Reals.Add (Icoeff left) (Icoeff right))
            (Reals.Add (Jcoeff left) (Jcoeff right))
            (Reals.Add (Kcoeff left) (Kcoeff right)).

    Definition Neg (left: Hamilton) : Hamilton
        := Quaternion (Reals.Neg (Re left)) (Reals.Neg (Icoeff left))
            (Reals.Neg (Jcoeff left)) (Reals.Neg (Kcoeff left)).

    Definition Conj (left: Hamilton) : Hamilton
        := Quaternion (Re left) (Reals.Neg (Icoeff left))
            (Reals.Neg (Jcoeff left)) (Reals.Neg (Kcoeff left)).

    Definition Norm_squared (left: Hamilton) : Reals.Real
        := Reals.Add (Reals.Add (Reals.Add
            (Reals.Mul (Re left) (Re left))
            (Reals.Mul (Icoeff left) (Icoeff left)))
            (Reals.Mul (Jcoeff left) (Jcoeff left)))
            (Reals.Mul (Kcoeff left) (Kcoeff left)).

    Definition Mul (left: Hamilton) (right : Hamilton) : Hamilton
        := Quaternion (Reals.Add (Re left) (Re right))
            (Reals.Add (Icoeff left) (Icoeff right))
            (Reals.Add (Jcoeff left) (Jcoeff right))
            (Reals.Add (Kcoeff left) (Kcoeff right)).

    Definition Inv (left: Hamilton)
        (not_zero : not (eq left
             (Quaternion Reals.zero Reals.zero Reals.zero Reals.zero)))
        : Hamilton
        := Quaternion (Re left)
            (Icoeff left) (Jcoeff left) (Kcoeff left).

    Axiom Add_unique_left:
        forall (left1: Hamilton) (left2: Hamilton) (right: Hamilton)
        (sums_are_equal : eq (Add left1 right) (Add left2 right)),
        eq left1 left2.

    Axiom Add_unique_right:
        forall (left: Hamilton) (right1: Hamilton) (right2: Hamilton)
        (sums_are_equal : eq (Add left right1) (Add left right2)),
        eq right1 right2.

    Axiom Add_unique_sum:
        forall (left: Hamilton) (right: Hamilton)
        (sum1: Hamilton) (sum2: Hamilton)
        (eq1: eq (Add left right) sum1)
        (eq2: eq (Add left right) sum2),
        eq sum1 sum2.

    Theorem Add_is_commutative :
        forall (left : Hamilton) (right : Hamilton),
        eq (Add left right) (Add right left).

    Proof.
        intro left.
        destruct left as [w_left x_left y_left z_left].
        intro right.
        destruct right as [w_right x_right y_right z_right].
        unfold Add.
        unfold Re.
        unfold Icoeff.
        unfold Jcoeff.
        unfold Kcoeff.
        rewrite (Reals.Add_is_commutative (w_left) (w_right)).
        rewrite (Reals.Add_is_commutative (x_right) (x_left)).
        rewrite (Reals.Add_is_commutative (y_left) (y_right)).
        rewrite (Reals.Add_is_commutative (z_right) (z_left)).
        reflexivity.
    Qed.

    Theorem Add_is_associative:
        forall (left: Hamilton) (middle: Hamilton) (right: Hamilton),
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
        forall (right: Hamilton), eq (Add zero right) (right).
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
        forall (left: Hamilton), eq (Add left zero) (left).

    Axiom Add_real_to_Neg_real:
        forall (x : Hamilton), eq (Add (x) (Neg x)) (zero).

    Axiom Add_Neg_real_to_real:
        forall (x : Hamilton), eq (Add (Neg x) (x)) (zero).

    Axiom Zero_is_Neg_zero: eq (zero) (Neg zero).

    Axiom Neg_zero_is_zero: eq (Neg zero) (zero).

    Axiom Mul_unique_left:
        forall (left1: Hamilton) (left2: Hamilton) (right: Hamilton)
        (sums_are_equal : eq (Mul left1 right) (Mul left2 right)),
        eq left1 left2.

    Axiom Mul_unique_right:
        forall (left: Hamilton) (right1: Hamilton) (right2: Hamilton)
        (sums_are_equal : eq (Mul left right1) (Mul left right2)),
        eq right1 right2.

    Axiom Mul_unique_product:
        forall (left: Hamilton) (right: Hamilton) (product1: Hamilton) (product2: Hamilton)
        (eq1: eq (Mul left right) product1)
        (eq2: eq (Mul left right) product2),
        eq product1 product2.

    Axiom Mul_is_commutative:
        forall (left: Hamilton) (right: Hamilton),
        eq (Mul left right) (Mul right left).

    Axiom Mul_is_associative:
        forall (left: Hamilton) (middle: Hamilton) (right: Hamilton),
        eq (Mul (left) (Mul middle right))
           (Mul (Mul left middle) (right)).

    Axiom Mul_is_distributive_left:
        forall (left: Hamilton) (middle: Hamilton) (right: Hamilton),
        eq (Mul (Add left middle) (right))
           (Add (Mul left right) (Mul middle right)).

    Axiom Mul_is_distributive_right:
        forall (left: Hamilton) (middle: Hamilton) (right: Hamilton),
        eq (Mul (left) (Add middle right))
           (Add (Mul left middle) (Mul left right)).

    Axiom Mul_identity_is_zero:
        forall (right: Hamilton), eq (Mul one right) (right).

    Axiom One_is_Mul_identity:
        forall (left: Hamilton), eq (Mul left one) (left).

    Axiom Mul_real_by_Inv_real:
        forall (left: Hamilton) (not_zero : not (eq left zero)),
        eq (Mul (left) (Inv left not_zero)) (one).

    Axiom Mul_Inv_real_by_real:
        forall (right: Hamilton) (not_zero : not (eq right zero)),
        eq (Mul (Inv right not_zero) (right)) (one).

End Quaternions.
