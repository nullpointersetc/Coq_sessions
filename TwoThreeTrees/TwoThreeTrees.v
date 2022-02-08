Require Coq.Structures.Equalities.
Require Coq.Structures.Orders.

Module TwoThreeTrees.

  Module TwoThreeTrees
      (Keys : Coq.Structures.Orders.LtBool)
      (Values : Coq.Structures.Equalities.Typ)
      : Coq.Structures.Equalities.Typ.

    Definition key_value_prod :=
        Coq.Init.Datatypes.prod (Keys.t) (Values.t).

    Inductive tree_type :=
        empty_tree
        | binary_node
          (before : tree_type)
          (first : key_value_prod)
          (after : tree_type) : tree_type
        | ternary_node
          (before : tree_type)
          (first : key_value_prod)
          (between : tree_type)
          (second : key_value_prod)
          (after : tree_type) : tree_type.

    Definition t := tree_type.

    Fixpoint bound (k : Keys.t)
        (tr : tree_type) : bool
      := (match tr
        with empty_tree =>
          false
        | binary_node (_ as before)
            (_ as first) (_ as after) =>
          (match Keys.ltb (k) (fst (first))
            with true =>
              bound (k) (before)
            | false =>
              (match Keys.ltb (fst (first)) (k)
                with true =>
                  bound (k) (after)
                | false =>
                  true
              end)
          end)
        | ternary_node (_ as before)
            (_ as first) (_ as between)
            (_ as second) (_ as after) =>
          (match Keys.ltb (k) (fst (first))
            with true =>
              bound (k) (before)
            | false =>
              (match Keys.ltb (fst (first)) (k)
                with true =>
                  (match Keys.ltb (k) (fst (second))
                    with true =>
                      bound (k) (between)
                    | false =>
                      (match Keys.ltb (fst (second)) (k)
                        with true =>
                          bound (k) (after)
                        | false =>
                          true
                      end)
                  end)
                | false =>
                  true
              end)
          end)
        end).

    Proposition bound_on_empty_is_false
        (k1 : Keys.t)
        : eq false (bound (k1) (empty_tree)).
    Proof.
      try unfold bound.
      reflexivity.
    Qed.

    Proposition bound_on_singleton_is_true
        (k1 : Keys.t) (v1 : Values.t)
        (eq1 : eq false (Keys.ltb k1 k1))
        : eq true (bound (k1)
          (binary_node (empty_tree)
            (pair k1 v1) (empty_tree))).
    Proof.
      try unfold bound.
      try unfold fst.
      rewrite <- eq1.
      reflexivity.
    Qed.

    Proposition bound_on_different_singleton_is_true_1
        (k1 : Keys.t) (v1 : Values.t)
        (k2 : Keys.t)
        (neq1 : eq true (Keys.ltb k1 k2))
        (neq2 : eq false (Keys.ltb k2 k1))
        : eq false (bound (k2)
          (binary_node (empty_tree)
            (pair k1 v1) (empty_tree))).
    Proof.
      try unfold bound.
      try unfold fst.
      try rewrite <- neq1.
      try rewrite <- neq2.
      reflexivity.
    Qed.

    Proposition bound_on_different_singleton_is_true_2
        (k1 : Keys.t) (v1 : Values.t)
        (k2 : Keys.t)
        (neq1 : eq false (Keys.ltb k1 k2))
        (neq2 : eq true (Keys.ltb k2 k1))
        : eq false (bound (k2)
          (binary_node (empty_tree)
            (pair k1 v1) (empty_tree))).
    Proof.
      try unfold bound.
      try unfold fst.
      try rewrite <- neq1.
      try rewrite <- neq2.
      reflexivity.
    Qed.


  End TwoThreeTrees.

End TwoThreeTrees.

