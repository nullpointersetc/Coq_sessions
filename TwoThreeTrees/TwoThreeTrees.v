Require Coq.Structures.Equalities.
Require Coq.Structures.Orders.

Module TwoThreeTrees.

  Module TwoThreeTreesFor
      (Keys : Coq.Structures.Orders.LtBool)
      (Values : Coq.Structures.Equalities.Typ)
      : Coq.Structures.Equalities.Typ.

    Definition key_value_prod :=
        Coq.Init.Datatypes.prod (Keys.t) (Values.t).

    Inductive tree_type :=
        empty_tree : tree_type
        | singleton_tree
          (kv : key_value_prod) : tree_type
        | doubleton_tree
          (first : key_value_prod)
          (second : key_value_prod) : tree_type
        | binary_root
          (before : subtree_type)
          (first : key_value_prod)
          (after : subtree_type) : tree_type
        | ternary_root
          (before : subtree_type)
          (first : key_value_prod)
          (between : subtree_type)
          (second : key_value_prod)
          (after : subtree_type) : tree_type
      with subtree_type :=
        singleton_subtree
          (kv : key_value_prod) : subtree_type
        | doubleton_subtree
          (first : key_value_prod)
          (second : key_value_prod) : subtree_type
        | binary_subtree
          (before : subtree_type)
          (first : key_value_prod)
          (after : subtree_type) : subtree_type
        | ternary_subtree
          (before : subtree_type)
          (first : key_value_prod)
          (between : subtree_type)
          (second : key_value_prod)
          (after : subtree_type) : subtree_type.

    Definition t := tree_type.

    Definition bound (k : Keys.t)
        (tr : tree_type) : bool
      := (let fix bound_1 (st : subtree_type)
          := (match st
              with singleton_subtree (_ as kv) =>
                (match (Keys.ltb (k) (fst (kv))),
                  (Keys.ltb (fst (kv)) (k))
                with true, _ =>
                  false
                | false, false =>
                  true
                | _, true =>
                  false
                end)
              | doubleton_subtree
                  (_ as first) (_ as second) =>
                (match (Keys.ltb (k) (fst (first))),
                  (Keys.ltb (fst (first)) (k)),
                  (Keys.ltb (k) (fst (second))),
                  (Keys.ltb (fst (second)) (k))
                with true, _, _, _ =>
                  false
                | false, false, _, _ =>
                  true
                | _, true, true, _ =>
                  false
                | _, _, false, false =>
                  true
                | _, _, _, true =>
                  false
                end)
              | binary_subtree
                  (_ as before)
                  (_ as kv) (_ as after) =>
                (match (Keys.ltb (k) (fst (kv))),
                  (Keys.ltb (fst (kv)) (k))
                with true, _ =>
                  bound_1 (before)
                | false, false =>
                  true
                | _, true =>
                  bound_1 (after)
                end)
              | ternary_subtree
                (_ as before)
                (_ as first)
                (_ as between)
                (_ as second)
                (_ as after) =>
                (match (Keys.ltb (k) (fst (first))),
                  (Keys.ltb (fst (first)) (k)),
                  (Keys.ltb (k) (fst (second))),
                  (Keys.ltb (fst (second)) (k))
                with true, _, _, _ =>
                  bound_1 (before)
                | false, false, _, _ =>
                  true
                | _, true, true, _ =>
                  bound_1 (between)
                | _, _, false, false =>
                  true
                | _, _, _, true =>
                  bound_1 (after)
                end)
            end)
        in match tr
        with empty_tree =>
          false
        | singleton_tree (_ as kv) =>
          (match (Keys.ltb (k) (fst (kv))),
              (Keys.ltb (fst (kv)) (k))
            with true, _ =>
              false
            | false, false =>
              true
            | _, true =>
              false
            end)
        | doubleton_tree
            (_ as first) (_ as second) =>
          (match (Keys.ltb (k) (fst (first))),
              (Keys.ltb (fst (first)) (k)),
              (Keys.ltb (k) (fst (second))),
              (Keys.ltb (fst (second)) (k))
            with true, _, _, _ =>
              false
            | false, false, _, _ =>
              true
            | _, true, true, _ =>
              false
            | _, _, false, false =>
              true
            | _, _, _, true =>
              false
            end)
        | binary_root (_ as before)
          (_ as first) (_ as after) =>
          (match (Keys.ltb (k) (fst (first))),
              (Keys.ltb (fst (first)) (k))
            with true, _ =>
              bound_1 (before)
            | false, false =>
              true
            | _, true =>
              bound_1 (after)
            end)
        | ternary_root
            (_ as before)
            (_ as first) (_ as between)
            (_ as second) (_ as after) =>
          (match (Keys.ltb (k) (fst (first))),
              (Keys.ltb (fst (first)) (k)),
              (Keys.ltb (k) (fst (second))),
              (Keys.ltb (fst (second)) (k))
            with true, _, _, _ =>
              bound_1 (before)
            | false, false, _, _ =>
              true
            | _, true, true, _ =>
              bound_1 (between)
            | _, _, false, false =>
              true
            | _, _, _, true =>
              bound_1 (after)
            end)
        end).

    Proposition bound_on_empty_is_false
        (k1 : Keys.t)
        : eq false (bound (k1) (empty_tree)).
    Proof.
      try unfold bound.
      reflexivity.
    Defined.

    Proposition bound_on_singleton_is_true
        (k1 : Keys.t) (v1 : Values.t)
        (eq1 : eq false (Keys.ltb k1 k1))
        : eq true (bound (k1)
          (singleton_tree (pair k1 v1))).
    Proof.
      try unfold bound.
      try unfold fst.
      rewrite <- eq1.
      reflexivity.
    Defined.

    Proposition bound_on_different_singleton_is_true_1
        (k1 : Keys.t) (v1 : Values.t)
        (k2 : Keys.t)
        (neq1 : eq true (Keys.ltb k1 k2))
        (neq2 : eq false (Keys.ltb k2 k1))
        : eq false (bound (k2)
          (singleton_tree (pair k1 v1))).
    Proof.
      try unfold bound.
      try unfold fst.
      try rewrite <- neq1.
      try rewrite <- neq2.
      reflexivity.
    Defined.

    Proposition bound_on_different_singleton_is_true_2
        (k1 : Keys.t) (v1 : Values.t)
        (k2 : Keys.t)
        (neq1 : eq false (Keys.ltb k1 k2))
        (neq2 : eq true (Keys.ltb k2 k1))
        : eq false (bound (k2)
          (singleton_tree (pair k1 v1))).
    Proof.
      try unfold bound.
      try unfold fst.
      try rewrite <- neq1.
      try rewrite <- neq2.
      reflexivity.
    Defined.

    Proposition restructuring_one
      (k1 : Keys.t) (v1 : Values.t)
      (k2 : Keys.t) (v2 : Values.t)
      (k3 : Keys.t) (v3 : Values.t)
      (k4 : Keys.t) (v4 : Values.t)
      (k5 : Keys.t) (v5 : Values.t)
      (k6 : Keys.t) (v6 : Values.t)
      (k7 : Keys.t) (v7 : Values.t)
      (k8 : Keys.t) (v8 : Values.t)
      (k9 : Keys.t) (v9 : Values.t)
      (k10 : Keys.t) (v10 : Values.t)
      (k11 : Keys.t) (v11 : Values.t)
      (k12 : Keys.t) (v12 : Values.t)
      (k13 : Keys.t) (v13 : Values.t)
      (k14 : Keys.t) (v14 : Values.t)
      (k15 : Keys.t) (v15 : Values.t)
      (k16 : Keys.t) (v16 : Values.t)
      (k17 : Keys.t) (v17 : Values.t)
      (k1_not_lt_k1 : eq false (Keys.ltb k1 k1))
      (k1_lt_k2 : eq true (Keys.ltb k1 k2))
      (k1_lt_k3 : eq true (Keys.ltb k1 k3))
      (k1_lt_k4 : eq true (Keys.ltb k1 k4))
      (k1_lt_k5 : eq true (Keys.ltb k1 k5))
      (k1_lt_k6 : eq true (Keys.ltb k1 k6))
      (k1_lt_k7 : eq true (Keys.ltb k1 k7))
      (k1_lt_k8 : eq true (Keys.ltb k1 k8))
      (k1_lt_k9 : eq true (Keys.ltb k1 k9))
      (k1_lt_k10 : eq true (Keys.ltb k1 k10))
      (k1_lt_k11 : eq true (Keys.ltb k1 k11))
      (k1_lt_k12 : eq true (Keys.ltb k1 k12))
      (k1_lt_k13 : eq true (Keys.ltb k1 k13))
      (k1_lt_k14 : eq true (Keys.ltb k1 k14))
      (k1_lt_k15 : eq true (Keys.ltb k1 k15))
      (k1_lt_k16 : eq true (Keys.ltb k1 k16))
      (k1_lt_k17 : eq true (Keys.ltb k1 k17))
      (k2_not_lt_k1 : eq false (Keys.ltb k2 k1))
      (k2_not_lt_k2 : eq false (Keys.ltb k2 k2))
      (k2_lt_k3 : eq true (Keys.ltb k2 k3))
      (k2_lt_k4 : eq true (Keys.ltb k2 k4))
      (k2_lt_k5 : eq true (Keys.ltb k2 k5))
      (k2_lt_k6 : eq true (Keys.ltb k2 k6))
      (k2_lt_k7 : eq true (Keys.ltb k2 k7))
      (k2_lt_k8 : eq true (Keys.ltb k2 k8))
      (k2_lt_k9 : eq true (Keys.ltb k2 k9))
      (k2_lt_k10 : eq true (Keys.ltb k2 k10))
      (k2_lt_k11 : eq true (Keys.ltb k2 k11))
      (k2_lt_k12 : eq true (Keys.ltb k2 k12))
      (k2_lt_k13 : eq true (Keys.ltb k2 k13))
      (k2_lt_k14 : eq true (Keys.ltb k2 k14))
      (k2_lt_k15 : eq true (Keys.ltb k2 k15))
      (k2_lt_k16 : eq true (Keys.ltb k2 k16))
      (k2_lt_k17 : eq true (Keys.ltb k2 k17))
      (k3_not_lt_k1 : eq false (Keys.ltb k3 k1))
      (k3_not_lt_k2 : eq false (Keys.ltb k3 k2))
      (k3_not_lt_k3 : eq false (Keys.ltb k3 k3))
      (k3_lt_k4 : eq true (Keys.ltb k3 k4))
      (k3_lt_k5 : eq true (Keys.ltb k3 k5))
      (k3_lt_k6 : eq true (Keys.ltb k3 k6))
      (k3_lt_k7 : eq true (Keys.ltb k3 k7))
      (k3_lt_k8 : eq true (Keys.ltb k3 k8))
      (k3_lt_k9 : eq true (Keys.ltb k3 k9))
      (k3_lt_k10 : eq true (Keys.ltb k3 k10))
      (k3_lt_k11 : eq true (Keys.ltb k3 k11))
      (k3_lt_k12 : eq true (Keys.ltb k3 k12))
      (k3_lt_k13 : eq true (Keys.ltb k3 k13))
      (k3_lt_k14 : eq true (Keys.ltb k3 k14))
      (k3_lt_k15 : eq true (Keys.ltb k3 k15))
      (k3_lt_k16 : eq true (Keys.ltb k3 k16))
      (k3_lt_k17 : eq true (Keys.ltb k3 k17))
      (k4_not_lt_k1 : eq false (Keys.ltb k4 k1))
      (k4_not_lt_k2 : eq false (Keys.ltb k4 k2))
      (k4_not_lt_k3 : eq false (Keys.ltb k4 k3))
      (k4_not_lt_k4 : eq false (Keys.ltb k4 k4))
      (k4_lt_k5 : eq true (Keys.ltb k4 k5))
      (k4_lt_k6 : eq true (Keys.ltb k4 k6))
      (k4_lt_k7 : eq true (Keys.ltb k4 k7))
      (k4_lt_k8 : eq true (Keys.ltb k4 k8))
      (k4_lt_k9 : eq true (Keys.ltb k4 k9))
      (k4_lt_k10 : eq true (Keys.ltb k4 k10))
      (k4_lt_k11 : eq true (Keys.ltb k4 k11))
      (k4_lt_k12 : eq true (Keys.ltb k4 k12))
      (k4_lt_k13 : eq true (Keys.ltb k4 k13))
      (k4_lt_k14 : eq true (Keys.ltb k4 k14))
      (k4_lt_k15 : eq true (Keys.ltb k4 k15))
      (k4_lt_k16 : eq true (Keys.ltb k4 k16))
      (k4_lt_k17 : eq true (Keys.ltb k4 k17))
      (k5_not_lt_k1 : eq false (Keys.ltb k5 k1))
      (k5_not_lt_k2 : eq false (Keys.ltb k5 k2))
      (k5_not_lt_k3 : eq false (Keys.ltb k5 k3))
      (k5_not_lt_k4 : eq false (Keys.ltb k5 k4))
      (k5_not_lt_k5 : eq false (Keys.ltb k5 k5))
      (k5_lt_k6 : eq true (Keys.ltb k5 k6))
      (k5_lt_k7 : eq true (Keys.ltb k5 k7))
      (k5_lt_k8 : eq true (Keys.ltb k5 k8))
      (k5_lt_k9 : eq true (Keys.ltb k5 k9))
      (k5_lt_k10 : eq true (Keys.ltb k5 k10))
      (k5_lt_k11 : eq true (Keys.ltb k5 k11))
      (k5_lt_k12 : eq true (Keys.ltb k5 k12))
      (k5_lt_k13 : eq true (Keys.ltb k5 k13))
      (k5_lt_k14 : eq true (Keys.ltb k5 k14))
      (k5_lt_k15 : eq true (Keys.ltb k5 k15))
      (k5_lt_k16 : eq true (Keys.ltb k5 k16))
      (k5_lt_k17 : eq true (Keys.ltb k5 k17))
      (k6_not_lt_k1 : eq false (Keys.ltb k6 k1))
      (k6_not_lt_k2 : eq false (Keys.ltb k6 k2))
      (k6_not_lt_k3 : eq false (Keys.ltb k6 k3))
      (k6_not_lt_k4 : eq false (Keys.ltb k6 k4))
      (k6_not_lt_k5 : eq false (Keys.ltb k6 k5))
      (k6_not_lt_k6 : eq false (Keys.ltb k6 k6))
      (k6_lt_k7 : eq true (Keys.ltb k6 k7))
      (k6_lt_k8 : eq true (Keys.ltb k6 k8))
      (k6_lt_k9 : eq true (Keys.ltb k6 k9))
      (k6_lt_k10 : eq true (Keys.ltb k6 k10))
      (k6_lt_k11 : eq true (Keys.ltb k6 k11))
      (k6_lt_k12 : eq true (Keys.ltb k6 k12))
      (k6_lt_k13 : eq true (Keys.ltb k6 k13))
      (k6_lt_k14 : eq true (Keys.ltb k6 k14))
      (k6_lt_k15 : eq true (Keys.ltb k6 k15))
      (k6_lt_k16 : eq true (Keys.ltb k6 k16))
      (k6_lt_k17 : eq true (Keys.ltb k6 k17))
      (k7_not_lt_k1 : eq false (Keys.ltb k7 k1))
      (k7_not_lt_k2 : eq false (Keys.ltb k7 k2))
      (k7_not_lt_k3 : eq false (Keys.ltb k7 k3))
      (k7_not_lt_k4 : eq false (Keys.ltb k7 k4))
      (k7_not_lt_k5 : eq false (Keys.ltb k7 k5))
      (k7_not_lt_k6 : eq false (Keys.ltb k7 k6))
      (k7_not_lt_k7 : eq false (Keys.ltb k7 k7))
      (k7_lt_k8 : eq true (Keys.ltb k7 k8))
      (k7_lt_k9 : eq true (Keys.ltb k7 k9))
      (k7_lt_k10 : eq true (Keys.ltb k7 k10))
      (k7_lt_k11 : eq true (Keys.ltb k7 k11))
      (k7_lt_k12 : eq true (Keys.ltb k7 k12))
      (k7_lt_k13 : eq true (Keys.ltb k7 k13))
      (k7_lt_k14 : eq true (Keys.ltb k7 k14))
      (k7_lt_k15 : eq true (Keys.ltb k7 k15))
      (k7_lt_k16 : eq true (Keys.ltb k7 k16))
      (k7_lt_k17 : eq true (Keys.ltb k7 k17))
      (k8_not_lt_k1 : eq false (Keys.ltb k8 k1))
      (k8_not_lt_k2 : eq false (Keys.ltb k8 k2))
      (k8_not_lt_k3 : eq false (Keys.ltb k8 k3))
      (k8_not_lt_k4 : eq false (Keys.ltb k8 k4))
      (k8_not_lt_k5 : eq false (Keys.ltb k8 k5))
      (k8_not_lt_k6 : eq false (Keys.ltb k8 k6))
      (k8_not_lt_k7 : eq false (Keys.ltb k8 k7))
      (k8_not_lt_k8 : eq false (Keys.ltb k8 k8))
      (k8_lt_k9 : eq true (Keys.ltb k8 k9))
      (k8_lt_k10 : eq true (Keys.ltb k8 k10))
      (k8_lt_k11 : eq true (Keys.ltb k8 k11))
      (k8_lt_k12 : eq true (Keys.ltb k8 k12))
      (k8_lt_k13 : eq true (Keys.ltb k8 k13))
      (k8_lt_k14 : eq true (Keys.ltb k8 k14))
      (k8_lt_k15 : eq true (Keys.ltb k8 k15))
      (k8_lt_k16 : eq true (Keys.ltb k8 k16))
      (k8_lt_k17 : eq true (Keys.ltb k8 k17))
      (k9_not_lt_k1 : eq false (Keys.ltb k9 k1))
      (k9_not_lt_k2 : eq false (Keys.ltb k9 k2))
      (k9_not_lt_k3 : eq false (Keys.ltb k9 k3))
      (k9_not_lt_k4 : eq false (Keys.ltb k9 k4))
      (k9_not_lt_k5 : eq false (Keys.ltb k9 k5))
      (k9_not_lt_k6 : eq false (Keys.ltb k9 k6))
      (k9_not_lt_k7 : eq false (Keys.ltb k9 k7))
      (k9_not_lt_k8 : eq false (Keys.ltb k9 k8))
      (k9_not_lt_k9 : eq false (Keys.ltb k9 k9))
      (k9_lt_k10 : eq true (Keys.ltb k9 k10))
      (k9_lt_k11 : eq true (Keys.ltb k9 k11))
      (k9_lt_k12 : eq true (Keys.ltb k9 k12))
      (k9_lt_k13 : eq true (Keys.ltb k9 k13))
      (k9_lt_k14 : eq true (Keys.ltb k9 k14))
      (k9_lt_k15 : eq true (Keys.ltb k9 k15))
      (k9_lt_k16 : eq true (Keys.ltb k9 k16))
      (k9_lt_k17 : eq true (Keys.ltb k9 k17))
      (k10_not_lt_k1 : eq false (Keys.ltb k10 k1))
      (k10_not_lt_k2 : eq false (Keys.ltb k10 k2))
      (k10_not_lt_k3 : eq false (Keys.ltb k10 k3))
      (k10_not_lt_k4 : eq false (Keys.ltb k10 k4))
      (k10_not_lt_k5 : eq false (Keys.ltb k10 k5))
      (k10_not_lt_k6 : eq false (Keys.ltb k10 k6))
      (k10_not_lt_k7 : eq false (Keys.ltb k10 k7))
      (k10_not_lt_k8 : eq false (Keys.ltb k10 k8))
      (k10_not_lt_k9 : eq false (Keys.ltb k10 k9))
      (k10_not_lt_k10 : eq false (Keys.ltb k10 k10))
      (k10_lt_k11 : eq true (Keys.ltb k10 k11))
      (k10_lt_k12 : eq true (Keys.ltb k10 k12))
      (k10_lt_k13 : eq true (Keys.ltb k10 k13))
      (k10_lt_k14 : eq true (Keys.ltb k10 k14))
      (k10_lt_k15 : eq true (Keys.ltb k10 k15))
      (k10_lt_k16 : eq true (Keys.ltb k10 k16))
      (k10_lt_k17 : eq true (Keys.ltb k10 k17))
      (k11_not_lt_k1 : eq false (Keys.ltb k11 k1))
      (k11_not_lt_k2 : eq false (Keys.ltb k11 k2))
      (k11_not_lt_k3 : eq false (Keys.ltb k11 k3))
      (k11_not_lt_k4 : eq false (Keys.ltb k11 k4))
      (k11_not_lt_k5 : eq false (Keys.ltb k11 k5))
      (k11_not_lt_k6 : eq false (Keys.ltb k11 k6))
      (k11_not_lt_k7 : eq false (Keys.ltb k11 k7))
      (k11_not_lt_k8 : eq false (Keys.ltb k11 k8))
      (k11_not_lt_k9 : eq false (Keys.ltb k11 k9))
      (k11_not_lt_k10 : eq false (Keys.ltb k11 k10))
      (k11_not_lt_k11 : eq false (Keys.ltb k11 k11))
      (k11_lt_k12 : eq true (Keys.ltb k11 k12))
      (k11_lt_k13 : eq true (Keys.ltb k11 k13))
      (k11_lt_k14 : eq true (Keys.ltb k11 k14))
      (k11_lt_k15 : eq true (Keys.ltb k11 k15))
      (k11_lt_k16 : eq true (Keys.ltb k11 k16))
      (k11_lt_k17 : eq true (Keys.ltb k11 k17))
      (k12_not_lt_k1 : eq false (Keys.ltb k12 k1))
      (k12_not_lt_k2 : eq false (Keys.ltb k12 k2))
      (k12_not_lt_k3 : eq false (Keys.ltb k12 k3))
      (k12_not_lt_k4 : eq false (Keys.ltb k12 k4))
      (k12_not_lt_k5 : eq false (Keys.ltb k12 k5))
      (k12_not_lt_k6 : eq false (Keys.ltb k12 k6))
      (k12_not_lt_k7 : eq false (Keys.ltb k12 k7))
      (k12_not_lt_k8 : eq false (Keys.ltb k12 k8))
      (k12_not_lt_k9 : eq false (Keys.ltb k12 k9))
      (k12_not_lt_k10 : eq false (Keys.ltb k12 k10))
      (k12_not_lt_k11 : eq false (Keys.ltb k12 k11))
      (k12_not_lt_k12 : eq false (Keys.ltb k12 k12))
      (k12_lt_k13 : eq true (Keys.ltb k12 k13))
      (k12_lt_k14 : eq true (Keys.ltb k12 k14))
      (k12_lt_k15 : eq true (Keys.ltb k12 k15))
      (k12_lt_k16 : eq true (Keys.ltb k12 k16))
      (k12_lt_k17 : eq true (Keys.ltb k12 k17))
      (k13_not_lt_k1 : eq false (Keys.ltb k13 k1))
      (k13_not_lt_k2 : eq false (Keys.ltb k13 k2))
      (k13_not_lt_k3 : eq false (Keys.ltb k13 k3))
      (k13_not_lt_k4 : eq false (Keys.ltb k13 k4))
      (k13_not_lt_k5 : eq false (Keys.ltb k13 k5))
      (k13_not_lt_k6 : eq false (Keys.ltb k13 k6))
      (k13_not_lt_k7 : eq false (Keys.ltb k13 k7))
      (k13_not_lt_k8 : eq false (Keys.ltb k13 k8))
      (k13_not_lt_k9 : eq false (Keys.ltb k13 k9))
      (k13_not_lt_k10 : eq false (Keys.ltb k13 k10))
      (k13_not_lt_k11 : eq false (Keys.ltb k13 k11))
      (k13_not_lt_k12 : eq false (Keys.ltb k13 k12))
      (k13_not_lt_k13 : eq false (Keys.ltb k13 k13))
      (k13_lt_k14 : eq true (Keys.ltb k13 k14))
      (k13_lt_k15 : eq true (Keys.ltb k13 k15))
      (k13_lt_k16 : eq true (Keys.ltb k13 k16))
      (k13_lt_k17 : eq true (Keys.ltb k13 k17))
      (k14_not_lt_k1 : eq false (Keys.ltb k14 k1))
      (k14_not_lt_k2 : eq false (Keys.ltb k14 k2))
      (k14_not_lt_k3 : eq false (Keys.ltb k14 k3))
      (k14_not_lt_k4 : eq false (Keys.ltb k14 k4))
      (k14_not_lt_k5 : eq false (Keys.ltb k14 k5))
      (k14_not_lt_k6 : eq false (Keys.ltb k14 k6))
      (k14_not_lt_k7 : eq false (Keys.ltb k14 k7))
      (k14_not_lt_k8 : eq false (Keys.ltb k14 k8))
      (k14_not_lt_k9 : eq false (Keys.ltb k14 k9))
      (k14_not_lt_k10 : eq false (Keys.ltb k14 k10))
      (k14_not_lt_k11 : eq false (Keys.ltb k14 k11))
      (k14_not_lt_k12 : eq false (Keys.ltb k14 k12))
      (k14_not_lt_k13 : eq false (Keys.ltb k14 k13))
      (k14_not_lt_k14 : eq false (Keys.ltb k14 k14))
      (k14_lt_k15 : eq true (Keys.ltb k14 k15))
      (k14_lt_k16 : eq true (Keys.ltb k14 k16))
      (k14_lt_k17 : eq true (Keys.ltb k14 k17))
      (k15_not_lt_k1 : eq false (Keys.ltb k15 k1))
      (k15_not_lt_k2 : eq false (Keys.ltb k15 k2))
      (k15_not_lt_k3 : eq false (Keys.ltb k15 k3))
      (k15_not_lt_k4 : eq false (Keys.ltb k15 k4))
      (k15_not_lt_k5 : eq false (Keys.ltb k15 k5))
      (k15_not_lt_k6 : eq false (Keys.ltb k15 k6))
      (k15_not_lt_k7 : eq false (Keys.ltb k15 k7))
      (k15_not_lt_k8 : eq false (Keys.ltb k15 k8))
      (k15_not_lt_k9 : eq false (Keys.ltb k15 k9))
      (k15_not_lt_k10 : eq false (Keys.ltb k15 k10))
      (k15_not_lt_k11 : eq false (Keys.ltb k15 k11))
      (k15_not_lt_k12 : eq false (Keys.ltb k15 k12))
      (k15_not_lt_k13 : eq false (Keys.ltb k15 k13))
      (k15_not_lt_k14 : eq false (Keys.ltb k15 k14))
      (k15_not_lt_k15 : eq false (Keys.ltb k15 k15))
      (k15_lt_k16 : eq true (Keys.ltb k15 k16))
      (k15_lt_k17 : eq true (Keys.ltb k15 k17))
      (k16_not_lt_k1 : eq false (Keys.ltb k16 k1))
      (k16_not_lt_k2 : eq false (Keys.ltb k16 k2))
      (k16_not_lt_k3 : eq false (Keys.ltb k16 k3))
      (k16_not_lt_k4 : eq false (Keys.ltb k16 k4))
      (k16_not_lt_k5 : eq false (Keys.ltb k16 k5))
      (k16_not_lt_k6 : eq false (Keys.ltb k16 k6))
      (k16_not_lt_k7 : eq false (Keys.ltb k16 k7))
      (k16_not_lt_k8 : eq false (Keys.ltb k16 k8))
      (k16_not_lt_k9 : eq false (Keys.ltb k16 k9))
      (k16_not_lt_k10 : eq false (Keys.ltb k16 k10))
      (k16_not_lt_k11 : eq false (Keys.ltb k16 k11))
      (k16_not_lt_k12 : eq false (Keys.ltb k16 k12))
      (k16_not_lt_k13 : eq false (Keys.ltb k16 k13))
      (k16_not_lt_k14 : eq false (Keys.ltb k16 k14))
      (k16_not_lt_k15 : eq false (Keys.ltb k16 k15))
      (k16_not_lt_k16 : eq false (Keys.ltb k16 k16))
      (k16_lt_k17 : eq true (Keys.ltb k16 k17))
      (k17_not_lt_k1 : eq false (Keys.ltb k17 k1))
      (k17_not_lt_k2 : eq false (Keys.ltb k17 k2))
      (k17_not_lt_k3 : eq false (Keys.ltb k17 k3))
      (k17_not_lt_k4 : eq false (Keys.ltb k17 k4))
      (k17_not_lt_k5 : eq false (Keys.ltb k17 k5))
      (k17_not_lt_k6 : eq false (Keys.ltb k17 k6))
      (k17_not_lt_k7 : eq false (Keys.ltb k17 k7))
      (k17_not_lt_k8 : eq false (Keys.ltb k17 k8))
      (k17_not_lt_k9 : eq false (Keys.ltb k17 k9))
      (k17_not_lt_k10 : eq false (Keys.ltb k17 k10))
      (k17_not_lt_k11 : eq false (Keys.ltb k17 k11))
      (k17_not_lt_k12 : eq false (Keys.ltb k17 k12))
      (k17_not_lt_k13 : eq false (Keys.ltb k17 k13))
      (k17_not_lt_k14 : eq false (Keys.ltb k17 k14))
      (k17_not_lt_k15 : eq false (Keys.ltb k17 k15))
      (k17_not_lt_k16 : eq false (Keys.ltb k17 k16))
      (k17_not_lt_k17 : eq false (Keys.ltb k17 k17))
      (lt_not_reflexive : forall (x : Keys.t), eq false (Keys.ltb x x))
      (lt_not_symmetric : forall (x : Keys.t)
        (y : Keys.t)
        (x_lt_y : eq true (Keys.ltb (x) (y))),
        eq false (Keys.ltb y x))
      (lt_transitive : forall (x : Keys.t)
        (y : Keys.t) (z : Keys.t)
        (x_lt_y : eq true (Keys.ltb x y))
        (y_lt_z : eq true (Keys.ltb y z)),
        eq true (Keys.ltb x z))
      (tr1 : tree_type)
      (tr1_eq : eq tr1
        (ternary_root
          (ternary_subtree
            (singleton_subtree (pair k1 v1))
            (pair k2 v2)
            (singleton_subtree (pair k3 v3))
            (pair k4 v4)
            (singleton_subtree (pair k5 v5)))
          (pair k6 v6)
          (ternary_subtree
            (singleton_subtree (pair k7 v7))
            (pair k8 v8)
            (singleton_subtree (pair k9 v9))
            (pair k10 v10)
            (singleton_subtree (pair k11 v11)))
          (pair k12 v12)
          (ternary_subtree
            (singleton_subtree (pair k13 v13))
            (pair k14 v14)
            (singleton_subtree (pair k15 v15))
            (pair k16 v16)
            (singleton_subtree (pair k17 v17)))))
      (tr2 : tree_type)
      (tr2_eq : eq tr2
        (binary_root
          (binary_subtree
            (binary_subtree
              (singleton_subtree (pair k1 v1))
              (pair k2 v2)
              (singleton_subtree (pair k3 v3)))
            (pair k4 v4)
            (binary_subtree
              (singleton_subtree (pair k5 v5))
              (pair k6 v6)
              (singleton_subtree (pair k7 v7))))
          (pair k8 v8)
          (binary_subtree
            (binary_subtree
              (singleton_subtree (pair k9 v9))
              (pair k10 v10)
              (singleton_subtree (pair k11 v11)))
            (pair k12 v12)
            (ternary_subtree
              (singleton_subtree (pair k13 v13))
              (pair k14 v14)
              (singleton_subtree (pair k15 v15))
              (pair k16 v16)
              (singleton_subtree (pair k17 v17))))))
    : and (and (and (and (and (and (and (and (and (and (and
      (and (and (and (and (and (and (and (and (and (and (and
      (and (and (and (and (and (and (and (and (and (and (and
      (eq true (bound k1 tr1)) (eq true (bound k2 tr1)))
      (eq true (bound k3 tr1))) (eq true (bound k4 tr1)))
      (eq true (bound k5 tr1))) (eq true (bound k6 tr1)))
      (eq true (bound k7 tr1))) (eq true (bound k8 tr1)))
      (eq true (bound k9 tr1))) (eq true (bound k10 tr1)))
      (eq true (bound k11 tr1))) (eq true (bound k12 tr1)))
      (eq true (bound k13 tr1))) (eq true (bound k14 tr1)))
      (eq true (bound k15 tr1))) (eq true (bound k16 tr1)))
      (eq true (bound k17 tr1)))
      (eq true (bound k1 tr2))) (eq true (bound k2 tr2)))
      (eq true (bound k3 tr2))) (eq true (bound k4 tr2)))
      (eq true (bound k5 tr2))) (eq true (bound k6 tr2)))
      (eq true (bound k7 tr2))) (eq true (bound k8 tr2)))
      (eq true (bound k9 tr2))) (eq true (bound k10 tr2)))
      (eq true (bound k11 tr2))) (eq true (bound k12 tr2)))
      (eq true (bound k13 tr2))) (eq true (bound k14 tr2)))
      (eq true (bound k15 tr2))) (eq true (bound k16 tr2)))
      (eq true (bound k17 tr2)).
    Proof.
      rewrite -> tr1_eq.
      rewrite -> tr2_eq.
      unfold bound.
      unfold fst.
      try rewrite <- k1_not_lt_k1.
      try rewrite <- k1_lt_k2.
      try rewrite <- k1_lt_k3.
      try rewrite <- k1_lt_k4.
      try rewrite <- k1_lt_k5.
      try rewrite <- k1_lt_k6.
      try rewrite <- k1_lt_k7.
      try rewrite <- k1_lt_k8.
      try rewrite <- k1_lt_k9.
      try rewrite <- k1_lt_k10.
      try rewrite <- k1_lt_k11.
      try rewrite <- k1_lt_k12.
      try rewrite <- k1_lt_k13.
      try rewrite <- k1_lt_k14.
      try rewrite <- k1_lt_k15.
      try rewrite <- k1_lt_k16.
      try rewrite <- k1_lt_k17.
      try rewrite <- k2_not_lt_k1.
      try rewrite <- k2_not_lt_k2.
      try rewrite <- k2_lt_k3.
      try rewrite <- k2_lt_k4.
      try rewrite <- k2_lt_k5.
      try rewrite <- k2_lt_k6.
      try rewrite <- k2_lt_k7.
      try rewrite <- k2_lt_k8.
      try rewrite <- k2_lt_k9.
      try rewrite <- k2_lt_k10.
      try rewrite <- k2_lt_k11.
      try rewrite <- k2_lt_k12.
      try rewrite <- k2_lt_k13.
      try rewrite <- k2_lt_k14.
      try rewrite <- k2_lt_k15.
      try rewrite <- k2_lt_k16.
      try rewrite <- k2_lt_k17.
      try rewrite <- k3_not_lt_k1.
      try rewrite <- k3_not_lt_k2.
      try rewrite <- k3_not_lt_k3.
      try rewrite <- k3_lt_k4.
      try rewrite <- k3_lt_k5.
      try rewrite <- k3_lt_k6.
      try rewrite <- k3_lt_k7.
      try rewrite <- k3_lt_k8.
      try rewrite <- k3_lt_k9.
      try rewrite <- k3_lt_k10.
      try rewrite <- k3_lt_k11.
      try rewrite <- k3_lt_k12.
      try rewrite <- k3_lt_k13.
      try rewrite <- k3_lt_k14.
      try rewrite <- k3_lt_k15.
      try rewrite <- k3_lt_k16.
      try rewrite <- k3_lt_k17.
      try rewrite <- k4_not_lt_k1.
      try rewrite <- k4_not_lt_k2.
      try rewrite <- k4_not_lt_k3.
      try rewrite <- k4_not_lt_k4.
      try rewrite <- k4_lt_k5.
      try rewrite <- k4_lt_k6.
      try rewrite <- k4_lt_k7.
      try rewrite <- k4_lt_k8.
      try rewrite <- k4_lt_k9.
      try rewrite <- k4_lt_k10.
      try rewrite <- k4_lt_k11.
      try rewrite <- k4_lt_k12.
      try rewrite <- k4_lt_k13.
      try rewrite <- k4_lt_k14.
      try rewrite <- k4_lt_k15.
      try rewrite <- k4_lt_k16.
      try rewrite <- k4_lt_k17.
      try rewrite <- k5_not_lt_k1.
      try rewrite <- k5_not_lt_k2.
      try rewrite <- k5_not_lt_k3.
      try rewrite <- k5_not_lt_k4.
      try rewrite <- k5_not_lt_k5.
      try rewrite <- k5_lt_k6.
      try rewrite <- k5_lt_k7.
      try rewrite <- k5_lt_k8.
      try rewrite <- k5_lt_k9.
      try rewrite <- k5_lt_k10.
      try rewrite <- k5_lt_k11.
      try rewrite <- k5_lt_k12.
      try rewrite <- k5_lt_k13.
      try rewrite <- k5_lt_k14.
      try rewrite <- k5_lt_k15.
      try rewrite <- k5_lt_k16.
      try rewrite <- k5_lt_k17.
      try rewrite <- k6_not_lt_k1.
      try rewrite <- k6_not_lt_k2.
      try rewrite <- k6_not_lt_k3.
      try rewrite <- k6_not_lt_k4.
      try rewrite <- k6_not_lt_k5.
      try rewrite <- k6_not_lt_k6.
      try rewrite <- k6_lt_k7.
      try rewrite <- k6_lt_k8.
      try rewrite <- k6_lt_k9.
      try rewrite <- k6_lt_k10.
      try rewrite <- k6_lt_k11.
      try rewrite <- k6_lt_k12.
      try rewrite <- k6_lt_k13.
      try rewrite <- k6_lt_k14.
      try rewrite <- k6_lt_k15.
      try rewrite <- k6_lt_k16.
      try rewrite <- k6_lt_k17.
      try rewrite <- k7_not_lt_k1.
      try rewrite <- k7_not_lt_k2.
      try rewrite <- k7_not_lt_k3.
      try rewrite <- k7_not_lt_k4.
      try rewrite <- k7_not_lt_k5.
      try rewrite <- k7_not_lt_k6.
      try rewrite <- k7_not_lt_k7.
      try rewrite <- k7_lt_k8.
      try rewrite <- k7_lt_k9.
      try rewrite <- k7_lt_k10.
      try rewrite <- k7_lt_k11.
      try rewrite <- k7_lt_k12.
      try rewrite <- k7_lt_k13.
      try rewrite <- k7_lt_k14.
      try rewrite <- k7_lt_k15.
      try rewrite <- k7_lt_k16.
      try rewrite <- k7_lt_k17.
      try rewrite <- k8_not_lt_k2.
      try rewrite <- k8_not_lt_k1.
      try rewrite <- k8_not_lt_k3.
      try rewrite <- k8_not_lt_k4.
      try rewrite <- k8_not_lt_k5.
      try rewrite <- k8_not_lt_k6.
      try rewrite <- k8_not_lt_k7.
      try rewrite <- k8_not_lt_k8.
      try rewrite <- k8_lt_k9.
      try rewrite <- k8_lt_k10.
      try rewrite <- k8_lt_k11.
      try rewrite <- k8_lt_k12.
      try rewrite <- k8_lt_k13.
      try rewrite <- k8_lt_k14.
      try rewrite <- k8_lt_k15.
      try rewrite <- k8_lt_k16.
      try rewrite <- k8_lt_k17.
      try rewrite <- k9_not_lt_k1.
      try rewrite <- k9_not_lt_k2.
      try rewrite <- k9_not_lt_k3.
      try rewrite <- k9_not_lt_k4.
      try rewrite <- k9_not_lt_k5.
      try rewrite <- k9_not_lt_k6.
      try rewrite <- k9_not_lt_k7.
      try rewrite <- k9_not_lt_k8.
      try rewrite <- k9_not_lt_k9.
      try rewrite <- k9_lt_k10.
      try rewrite <- k9_lt_k11.
      try rewrite <- k9_lt_k12.
      try rewrite <- k9_lt_k13.
      try rewrite <- k9_lt_k14.
      try rewrite <- k9_lt_k15.
      try rewrite <- k9_lt_k16.
      try rewrite <- k9_lt_k17.
      try rewrite <- k10_not_lt_k1.
      try rewrite <- k10_not_lt_k2.
      try rewrite <- k10_not_lt_k3.
      try rewrite <- k10_not_lt_k4.
      try rewrite <- k10_not_lt_k5.
      try rewrite <- k10_not_lt_k6.
      try rewrite <- k10_not_lt_k7.
      try rewrite <- k10_not_lt_k8.
      try rewrite <- k10_not_lt_k9.
      try rewrite <- k10_not_lt_k10.
      try rewrite <- k10_lt_k11.
      try rewrite <- k10_lt_k12.
      try rewrite <- k10_lt_k13.
      try rewrite <- k10_lt_k14.
      try rewrite <- k10_lt_k15.
      try rewrite <- k10_lt_k16.
      try rewrite <- k10_lt_k17.
      try rewrite <- k11_not_lt_k1.
      try rewrite <- k11_not_lt_k2.
      try rewrite <- k11_not_lt_k3.
      try rewrite <- k11_not_lt_k4.
      try rewrite <- k11_not_lt_k5.
      try rewrite <- k11_not_lt_k6.
      try rewrite <- k11_not_lt_k7.
      try rewrite <- k11_not_lt_k8.
      try rewrite <- k11_not_lt_k9.
      try rewrite <- k11_not_lt_k10.
      try rewrite <- k11_not_lt_k11.
      try rewrite <- k11_lt_k12.
      try rewrite <- k11_lt_k13.
      try rewrite <- k11_lt_k14.
      try rewrite <- k11_lt_k15.
      try rewrite <- k11_lt_k16.
      try rewrite <- k11_lt_k17.
      try rewrite <- k12_not_lt_k1.
      try rewrite <- k12_not_lt_k2.
      try rewrite <- k12_not_lt_k3.
      try rewrite <- k12_not_lt_k4.
      try rewrite <- k12_not_lt_k5.
      try rewrite <- k12_not_lt_k6.
      try rewrite <- k12_not_lt_k7.
      try rewrite <- k12_not_lt_k8.
      try rewrite <- k12_not_lt_k9.
      try rewrite <- k12_not_lt_k10.
      try rewrite <- k12_not_lt_k11.
      try rewrite <- k12_not_lt_k12.
      try rewrite <- k12_lt_k13.
      try rewrite <- k12_lt_k14.
      try rewrite <- k12_lt_k15.
      try rewrite <- k12_lt_k16.
      try rewrite <- k12_lt_k17.
      try rewrite <- k13_not_lt_k1.
      try rewrite <- k13_not_lt_k2.
      try rewrite <- k13_not_lt_k3.
      try rewrite <- k13_not_lt_k4.
      try rewrite <- k13_not_lt_k5.
      try rewrite <- k13_not_lt_k6.
      try rewrite <- k13_not_lt_k7.
      try rewrite <- k13_not_lt_k8.
      try rewrite <- k13_not_lt_k9.
      try rewrite <- k13_not_lt_k10.
      try rewrite <- k13_not_lt_k11.
      try rewrite <- k13_not_lt_k12.
      try rewrite <- k13_not_lt_k13.
      try rewrite <- k13_lt_k14.
      try rewrite <- k13_lt_k15.
      try rewrite <- k13_lt_k16.
      try rewrite <- k13_lt_k17.
      try rewrite <- k14_not_lt_k1.
      try rewrite <- k14_not_lt_k2.
      try rewrite <- k14_not_lt_k3.
      try rewrite <- k14_not_lt_k4.
      try rewrite <- k14_not_lt_k5.
      try rewrite <- k14_not_lt_k6.
      try rewrite <- k14_not_lt_k7.
      try rewrite <- k14_not_lt_k8.
      try rewrite <- k14_not_lt_k9.
      try rewrite <- k14_not_lt_k10.
      try rewrite <- k14_not_lt_k11.
      try rewrite <- k14_not_lt_k12.
      try rewrite <- k14_not_lt_k13.
      try rewrite <- k14_not_lt_k14.
      try rewrite <- k14_lt_k15.
      try rewrite <- k14_lt_k16.
      try rewrite <- k14_lt_k17.
      try rewrite <- k15_not_lt_k1.
      try rewrite <- k15_not_lt_k2.
      try rewrite <- k15_not_lt_k3.
      try rewrite <- k15_not_lt_k4.
      try rewrite <- k15_not_lt_k5.
      try rewrite <- k15_not_lt_k6.
      try rewrite <- k15_not_lt_k7.
      try rewrite <- k15_not_lt_k8.
      try rewrite <- k15_not_lt_k9.
      try rewrite <- k15_not_lt_k10.
      try rewrite <- k15_not_lt_k11.
      try rewrite <- k15_not_lt_k12.
      try rewrite <- k15_not_lt_k13.
      try rewrite <- k15_not_lt_k14.
      try rewrite <- k15_not_lt_k15.
      try rewrite <- k15_lt_k16.
      try rewrite <- k15_lt_k17.
      try rewrite <- k16_not_lt_k1.
      try rewrite <- k16_not_lt_k2.
      try rewrite <- k16_not_lt_k3.
      try rewrite <- k16_not_lt_k4.
      try rewrite <- k16_not_lt_k5.
      try rewrite <- k16_not_lt_k6.
      try rewrite <- k16_not_lt_k7.
      try rewrite <- k16_not_lt_k8.
      try rewrite <- k16_not_lt_k9.
      try rewrite <- k16_not_lt_k10.
      try rewrite <- k16_not_lt_k11.
      try rewrite <- k16_not_lt_k12.
      try rewrite <- k16_not_lt_k13.
      try rewrite <- k16_not_lt_k14.
      try rewrite <- k16_not_lt_k15.
      try rewrite <- k16_not_lt_k16.
      try rewrite <- k16_lt_k17.
      try rewrite <- k17_not_lt_k1.
      try rewrite <- k17_not_lt_k2.
      try rewrite <- k17_not_lt_k3.
      try rewrite <- k17_not_lt_k4.
      try rewrite <- k17_not_lt_k5.
      try rewrite <- k17_not_lt_k6.
      try rewrite <- k17_not_lt_k7.
      try rewrite <- k17_not_lt_k8.
      try rewrite <- k17_not_lt_k9.
      try rewrite <- k17_not_lt_k10.
      try rewrite <- k17_not_lt_k11.
      try rewrite <- k17_not_lt_k12.
      try rewrite <- k17_not_lt_k13.
      try rewrite <- k17_not_lt_k14.
      try rewrite <- k17_not_lt_k15.
      try rewrite <- k17_not_lt_k16.
      try rewrite <- k17_not_lt_k17.
      split ; reflexivity.
    Defined.

  End TwoThreeTreesFor.

End TwoThreeTrees.

