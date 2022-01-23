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
			:= fun (k : Keys.t) (v : Values.t) (tr : tree_t) =>
				(match tr
				with empty_tree => singleton_tree (k_and_v (k) (v))
				| singleton_tree (_ as kv) =>
					(match Keys.ltb (k) (key_from (kv)),
						Keys.ltb (key_from (kv)) (k)
				with true, _ => doubleton_tree (d_leaf (k_and_v (k) (v)) (kv))
				| false, false => singleton_tree (k_and_v (k) (v))
				| _, true => doubleton_tree (d_leaf (kv) (k_and_v (k) (v)))
				end)
				| doubleton_tree (_) => tr
				| singleton_root (_) => tr
				| doubleton_root (_) => tr
				end).

	End Trees.
End TwoThreeTrees.
