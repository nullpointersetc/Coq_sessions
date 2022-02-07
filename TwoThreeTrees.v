Require Coq.Structures.Orders.
Require Coq.Structures.Equalities.

Module TwoThreeTrees.

	Module Trees (Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: Coq.Structures.Equalities.Typ.

		Import Coq.Init.Datatypes.

		Inductive tree_t :=
			empty_tree : tree_t
			| singleton_tree (kv : key_and_value_t) : tree_t
			| doubleton_tree (kvkv : doubleton_leaf_t) : tree_t
			| singleton_root (s : singleton_node_t) : tree_t
			| doubleton_root (d : doubleton_node_t) : tree_t
		with node_t :=
			singleton_node (s : singleton_node_t) : node_t
			| doubleton_node (d : doubleton_node_t) : node_t
			| singleton_leaf (kv : key_and_value_t) : node_t
			| doubleton_leaf (kvkv : doubleton_leaf_t) : node_t
		with key_and_value_t :=
			k_and_v (key : Keys.t) (value : Values.t) : key_and_value_t
		with doubleton_leaf_t :=
			d_leaf (first : key_and_value_t)
				(second : key_and_value_t) : doubleton_leaf_t
		with singleton_node_t :=
			s_node (left : node_t)
				(kv : key_and_value_t) (right : node_t) : singleton_node_t
		with doubleton_node_t :=
			d_node (left : node_t)
				(first : key_and_value_t) (middle : node_t)
				(kv : key_and_value_t) (right : node_t) : doubleton_node_t.

		Definition t := tree_t.

		Definition key_from (kv : key_and_value_t)
			:= match kv with k_and_v (_ as k) (_) => k end.

		Definition value_from (kv : key_and_value_t)
			:= match kv with k_and_v (_) (_ as v) => v end.

		Definition first_of (kvkv : doubleton_leaf_t)
			:= match kvkv with d_leaf (_ as f) (_) => f end.

		Definition first_key_of (kvkv : doubleton_leaf_t)
			:= key_from (first_of (kvkv)).

		Definition first_value_of (kvkv : doubleton_leaf_t)
			:= value_from (first_of (kvkv)).

		Definition second_of (kvkv : doubleton_leaf_t)
			:= match kvkv with d_leaf (_) (_ as s) => s end.

		Definition second_key_of (kvkv : doubleton_leaf_t)
			:= key_from (second_of (kvkv)).

		Definition second_value_of (kvkv : doubleton_leaf_t)
			:= value_from (second_of (kvkv)).

		Definition left_inside (s : singleton_node_t)
			:= match s with s_node (_ as L) (_) (_) => L end.

		Definition key_value_inside (s : singleton_node_t)
			:= match s with s_node (_) (_ as kv) (_) => kv end.

		Definition key_inside (s : singleton_node_t)
			:= key_from (key_value_inside (s)).

		Definition value_inside (s : singleton_node_t)
			:= value_from (key_value_inside (s)).

		Definition right_inside (s : singleton_node_t)
			:= match s with s_node (_) (_) (_ as R) => R end.

		Definition left_within (d : doubleton_node_t)
			:= match d with d_node (_ as L) (_) (_) (_) (_) => L end.

		Definition first_within (d : doubleton_node_t)
			:= match d with d_node (_) (_ as kv) (_) (_) (_) => kv end.

		Definition first_key_within (d : doubleton_node_t)
			:= key_from (first_within (d)).

		Definition first_value_within (d : doubleton_node_t)
			:= value_from (first_within (d)).

		Definition middle_within (d : doubleton_node_t)
			:= match d with d_node (_) (_) (_ as m) (_) (_) => m end.

		Definition second_within (d : doubleton_node_t)
			:= match d with d_node (_) (_) (_) (_ as kv) (_) => kv end.

		Definition second_key_within (d : doubleton_node_t)
			:= key_from (second_within (d)).

		Definition second_value_within (d : doubleton_node_t)
			:= value_from (second_within (d)).

		Definition right_within (d : doubleton_node_t)
			:= match d with d_node (_) (_) (_) (_) (_ as R) => R end.

		Definition value : Keys.t -> tree_t -> option (Values.t)
			:= fix value_one (k : Keys.t) (kv : key_and_value_t)
				:= (match Keys.ltb (k) (key_from (kv)),
					Keys.ltb (key_from (kv)) (k)
				with true, _ => None
				| false, false => Some (value_from (kv))
				| _, true => None
				end)
			with value_two (k : Keys.t) (kvkv : doubleton_leaf_t)
					: option (Values.t)
				:= (match Keys.ltb (k) (first_key_of (kvkv)),
					Keys.ltb (first_key_of (kvkv)) (k),
					Keys.ltb (k) (second_key_of (kvkv)),
					Keys.ltb (second_key_of (kvkv)) (k)
				with true, _, _, _ => None
				| false, false, _, _ => Some (first_value_of (kvkv))
				| _, true, true, _ => None
				| _, _, false, false => Some (second_value_of (kvkv))
				| _, _, _, true => None
				end)
			with value_three (k : Keys.t) (sn : singleton_node_t)
				:= (match Keys.ltb (k) (key_inside (sn)),
					Keys.ltb (key_inside (sn)) (k)
				with true, _ => value_five (k) (left_inside (sn))
				| false, false => Some (value_inside (sn))
				| _, true => value_five (k) (right_inside (sn))
				end)
			with value_four (k : Keys.t) (dn : doubleton_node_t)
				:= (match Keys.ltb (k) (first_key_within (dn)),
					Keys.ltb (first_key_within (dn)) (k),
					Keys.ltb (k) (second_key_within (dn)),
					Keys.ltb (second_key_within (dn)) (k)
				with true, _, _, _ => value_five (k) (left_within (dn))
				| false, false, _, _ => Some (first_value_within (dn))
				| _, true, true, _ => value_five (k) (middle_within (dn))
				| _, _, false, false => Some (second_value_within (dn))
				| _, _, _, true => value_five (k) (right_within (dn))
				end)
			with value_five (k : Keys.t) (node : node_t)
				:= (match node
				with singleton_leaf (_ as kv) => value_one (k) (kv)
				| doubleton_leaf (_ as kvkv) => value_two (k) (kvkv)
				| singleton_node (_ as sn) => value_three (k) (sn)
				| doubleton_node (_ as dn) => value_four (k) (dn)
				end)
			with value (k : Keys.t) (tr : tree_t)
				:= (match tr
				with empty_tree => None
				| singleton_tree (_ as kv) => value_one (k) (kv)
				| doubleton_tree (_ as kvkv) => value_two (k) (kvkv)
				| singleton_root (_ as sn) => value_three (k) (sn)
				| doubleton_root (_ as dn) => value_four (k) (dn)
				end)
			for value.

		Definition insert : Keys.t -> Values.t -> tree_t -> tree_t
			:= fix must_split_to_insert_1 (key1 : Keys.t) (val1 : Values.t) (node : node_t) : bool
				:= (match node
					with singleton_leaf (_ as kv) => false
					| doubleton_leaf (_ as kvkv) =>
						(match Keys.ltb (key1) (first_key_of (kvkv)),
							Keys.ltb (first_key_of (kvkv)) (key1),
							Keys.ltb (key1) (second_key_of (kvkv)),
							Keys.ltb (second_key_of (kvkv)) (key1)
						with true, _, _, _ => true
						| false, false, _, _ => false
						| _, true, true, _ => true
						| _, _, false, false => false
						| _, _, _, true => true
						end)
					| singleton_node (_ as sn) => false
					| doubleton_node (_ as dn) =>
						(match Keys.ltb (key1) (first_key_within (dn)),
							Keys.ltb (first_key_within (dn)) (key1),
							Keys.ltb (key1) (second_key_within (dn)),
							Keys.ltb (second_key_within (dn)) (key1)
						with true, _, _, _ => must_split_to_insert_1 (key1) (val1) (left_within (dn))
						| false, false, _, _ => false
						| _, true, true, _ => must_split_to_insert_1 (key1) (val1) (middle_within (dn))
						| _, _, false, false => false
						| _, _, _, true => must_split_to_insert_1 (key1) (val1) (right_within (dn))
						end)
					end)
			with must_split_to_insert_2 (key1 : Keys.t) (val1 : Values.t) (tr : tree_t) : bool
				:= (match tr
					with empty_tree (_ as kv) => false
					| singleton_tree (_ as kv) => false
					| doubleton_tree (_ as kvkv) =>
						(match Keys.ltb (key1) (first_key_of (kvkv)),
							Keys.ltb (first_key_of (kvkv)) (key1),
							Keys.ltb (key1) (second_key_of (kvkv)),
							Keys.ltb (second_key_of (kvkv)) (key1)
						with true, _, _, _ => true
						| false, false, _, _ => false
						| _, true, true, _ => true
						| _, _, false, false => false
						| _, _, _, true => true
						end)
					| singleton_root (_ as sn) => false
					| doubleton_root (_ as dn) =>
						(match Keys.ltb (key1) (first_key_within (dn)),
							Keys.ltb (first_key_within (dn)) (key1),
							Keys.ltb (key1) (second_key_within (dn)),
							Keys.ltb (second_key_within (dn)) (key1)
						with true, _, _, _ => must_split_to_insert_1 (key1) (val1) (left_within (dn))
						| false, false, _, _ => false
						| _, true, true, _ => must_split_to_insert_1 (key1) (val1) (middle_within (dn))
						| _, _, false, false => false
						| _, _, _, true => must_split_to_insert_1 (key1) (val1) (right_within (dn))
						end)
					end)
			with insert_node (key1 : Keys.t) (val1 : Values.t) (node : node_t) : node_t
				:= (match node
					with singleton_leaf (_ as kv) => singleton_leaf (k_and_v (key1) (val1))
					| doubleton_leaf (_ as kvkv) => singleton_leaf (k_and_v (key1) (val1))
					| singleton_node (_ as sn) => singleton_leaf (k_and_v (key1) (val1))
					| doubleton_node (_ as dn) => singleton_leaf (k_and_v (key1) (val1))
					end)
			with insert (key1 : Keys.t) (val1 : Values.t) (tr : tree_t)
				:= (match tr
					with empty_tree =>
						singleton_tree (k_and_v (key1) (val1))
					| singleton_tree (_ as kv) =>
						(match Keys.ltb (key1) (key_from (kv)),
							Keys.ltb (key_from (kv)) (key1)
						with true, _ =>
							doubleton_tree (d_leaf (k_and_v (key1) (val1)) (kv))
						| false, false =>
							singleton_tree (k_and_v (key1) (val1))
						| _, true =>
							doubleton_tree (d_leaf (kv) (k_and_v (key1) (val1)))
						end)
					| doubleton_tree (_ as kvkv) =>
						(match Keys.ltb (key1) (first_key_of (kvkv)),
							Keys.ltb (first_key_of (kvkv)) (key1),
							Keys.ltb (key1) (second_key_of (kvkv)),
							Keys.ltb (second_key_of (kvkv)) (key1)
						with true, _, _, _ =>
							singleton_root (s_node
								(singleton_leaf (k_and_v (key1) (val1)))
								(first_of (kvkv))
								(singleton_leaf (second_of (kvkv))))
						| false, false, _, _ =>
						  doubleton_tree (d_leaf
						  	(k_and_v (key1) (val1))
						  	(second_of (kvkv)))
						| _, true, true, _ =>
							singleton_root (s_node
								(singleton_leaf (first_of (kvkv)))
								(k_and_v (key1) (val1))
								(singleton_leaf (second_of (kvkv))))
						| _, _, false, false =>
						  doubleton_tree (d_leaf
						  	(first_of (kvkv))
						  	(k_and_v (key1) (val1)))
						| _, _, _, true =>
							singleton_root (s_node
								(singleton_leaf (first_of (kvkv)))
								(second_of (kvkv))
								(singleton_leaf (k_and_v (key1) (val1))))
						end)
					| singleton_root (_ as sn) =>
						(match Keys.ltb (key1) (key_inside (sn)),
							Keys.ltb (key_inside (sn)) (key1)
						with true, _ =>
							singleton_root (sn)
						| false, false =>
						  singleton_root (s_node
						  	(left_inside (sn))
						  	(k_and_v (key1) (val1))
						  	(right_inside (sn)))
						| _, true =>
							singleton_root (sn)
						end)
					| doubleton_root (_ as dn) =>
						(match Keys.ltb (key1) (first_key_within (dn)),
							Keys.ltb (first_key_within (dn)) (key1),
							Keys.ltb (key1) (second_key_within (dn)),
							Keys.ltb (second_key_within (dn)) (key1)
						with true, _, _, _ =>
							doubleton_root (dn)
						| false, false, _, _ =>
						  doubleton_root (dn)
						| _, true, true, _ =>
							doubleton_root (dn)
						| _, _, false, false =>
							doubleton_root (dn)
						| _, _, _, true =>
							doubleton_root (dn)
						end)
					end)
			for insert.

		Theorem insert_theorem_1 :
			forall key: Keys.t, forall val: Values.t,
			eq (insert (key) (val) (empty_tree))
			(singleton_tree (k_and_v (key) (val))).
		Proof.
			intro key.
			intro val.
			unfold insert.
			reflexivity.
		Qed.

		Theorem insert_theorem_2 :
			forall key1: Keys.t, forall val1: Values.t,
			forall key2: Keys.t, forall val2: Values.t,
			forall k1_lt_k2: eq true (Keys.ltb (key1) (key2)),
			forall k2_not_lt_k1: eq false (Keys.ltb (key2) (key1)),
			eq (insert (key1) (val1) (insert (key2) (val2) (empty_tree)))
			(doubleton_tree (d_leaf
						(k_and_v (key1) (val1))
						(k_and_v (key2) (val2)))).
		Proof.
			intro key1.
			intro val1.
			intro key2.
			intro val2.
			intro k1_lt_k2.
			intro k2_not_lt_k1.
			unfold insert.
			try unfold right_within.
			try unfold second_value_within.
			try unfold second_key_within.
			try unfold second_within.
			try unfold middle_within.
			try unfold first_value_within.
			try unfold first_key_within.
			try unfold first_within.
			try unfold left_within.
			try unfold right_inside.
			try unfold value_inside.
			try unfold key_inside.
			try unfold key_value_inside.
			try unfold left_inside.
			try unfold second_value_of.
			try unfold second_key_of.
			try unfold second_of.
			try unfold first_value_of.
			try unfold first_key_of.
			try unfold first_of.
			try unfold value_from.
			try unfold key_from.
			try rewrite <- k1_lt_k2.
			try rewrite <- k2_not_lt_k1.
			reflexivity.
		Qed.

		Theorem insert_theorem_3 :
			forall key1: Keys.t, forall val1: Values.t,
			forall key2: Keys.t, forall val2: Values.t,
			forall k1_not_lt_k2: eq false (Keys.ltb (key1) (key2)),
			forall k2_lt_k1: eq true (Keys.ltb (key2) (key1)),
			eq (insert (key1) (val1) (insert (key2) (val2) (empty_tree)))
			(doubleton_tree (d_leaf
						(k_and_v (key2) (val2))
						(k_and_v (key1) (val1)))).
		Proof.
			intro key1.
			intro val1.
			intro key2.
			intro val2.
			intro k1_not_lt_k2.
			intro k2_lt_k1.
			unfold insert.
			try unfold right_within.
			try unfold second_value_within.
			try unfold second_key_within.
			try unfold second_within.
			try unfold middle_within.
			try unfold first_value_within.
			try unfold first_key_within.
			try unfold first_within.
			try unfold left_within.
			try unfold right_inside.
			try unfold value_inside.
			try unfold key_inside.
			try unfold key_value_inside.
			try unfold left_inside.
			try unfold second_value_of.
			try unfold second_key_of.
			try unfold second_of.
			try unfold first_value_of.
			try unfold first_key_of.
			try unfold first_of.
			try unfold value_from.
			try unfold key_from.
			try rewrite <- k1_not_lt_k2.
			try rewrite <- k2_lt_k1.
			reflexivity.
		Qed.

		Theorem insert_theorem_4 :
			forall key1: Keys.t, forall val1: Values.t,
			forall key2: Keys.t, forall val2: Values.t,
			forall key3: Keys.t, forall val3: Values.t,
			forall k1_lt_k2: eq true (Keys.ltb (key1) (key2)),
			forall k2_not_lt_k1: eq false (Keys.ltb (key2) (key1)),
			forall k2_lt_k3: eq true (Keys.ltb (key2) (key3)),
			forall k3_not_lt_k2: eq false (Keys.ltb (key3) (key2)),
			eq (insert (key1) (val1) (insert (key2) (val2)
             (insert (key3) (val3) (empty_tree))))
			(singleton_root (s_node
						(singleton_leaf (k_and_v (key1) (val1)))
						(k_and_v (key2) (val2))
						(singleton_leaf (k_and_v (key3) (val3))))).
		Proof.
			intro key1.
			intro val1.
			intro key2.
			intro val2.
			intro key3.
			intro val3.
			intro k1_lt_k2.
			intro k2_not_lt_k1.
			intro k2_lt_k3.
			intro k3_not_lt_k2.
			unfold insert.
			try unfold right_within.
			try unfold second_value_within.
			try unfold second_key_within.
			try unfold second_within.
			try unfold middle_within.
			try unfold first_value_within.
			try unfold first_key_within.
			try unfold first_within.
			try unfold left_within.
			try unfold right_inside.
			try unfold value_inside.
			try unfold key_inside.
			try unfold key_value_inside.
			try unfold left_inside.
			try unfold second_value_of.
			try unfold second_key_of.
			try unfold second_of.
			try unfold first_value_of.
			try unfold first_key_of.
			try unfold first_of.
			try unfold value_from.
			try unfold key_from.
			try rewrite <- k2_lt_k3.
      try rewrite <- k3_not_lt_k2.
			try rewrite <- k1_lt_k2.
      try rewrite <- k2_not_lt_k1.
			reflexivity.
		Qed.

	End Trees.
End TwoThreeTrees.
