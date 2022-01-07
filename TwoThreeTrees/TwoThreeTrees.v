Require Coq.Structures.Orders.
Require Coq.Structures.Equalities.

Module TwoThreeTrees.

	Module Trees (Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: Coq.Structures.Equalities.Typ.

		Import Coq.Init.Datatypes.

		Inductive tree_t :=
			empty_tree : tree_t
			| singleton_tree (kv : key_value_t) : tree_t
			| doubleton_tree (kvkv : two_keys_values_t) : tree_t
			| singleton_root (s : singleton_node_t) : tree_t
			| doubleton_root (d : doubleton_node_t) : tree_t
		with node_t :=
			singleton_node (s : singleton_node_t) : node_t
			| doubleton_node (d : doubleton_node_t) : node_t
			| singleton_leaf (kv : key_value_t) : node_t
			| doubleton_leaf (kvkv : two_keys_values_t) : node_t
		with key_value_t :=
			kv_pair (key : Keys.t) (value : Values.t) : key_value_t
		with two_keys_values_t :=
			kvkv_pair (first : key_value_t)
				(second : key_value_t) : two_keys_values_t
		with singleton_node_t :=
			s_node (left : node_t)
				(kv : key_value_t) (right : node_t) : singleton_node_t
		with doubleton_node_t :=
			d_node (left : node_t)
				(first : key_value_t) (middle : node_t)
				(kv : key_value_t) (right : node_t) : doubleton_node_t.

		Definition t := tree_t.

		Module KV.
			Definition key (kv : key_value_t)
				:= match kv with kv_pair (_ as k) (_) => k end.

			Definition value (kv : key_value_t)
				:= match kv with kv_pair (_) (_ as v) => v end.

			Definition first (kvkv : two_keys_values_t)
				:= match kvkv with kvkv_pair (_ as f) (_) => f end.

			Definition first_key (kvkv : two_keys_values_t)
				:= key (first (kvkv)).

			Definition first_value (kvkv : two_keys_values_t)
				:= value (first (kvkv)).

			Definition second (kvkv : two_keys_values_t)
				:= match kvkv with kvkv_pair (_) (_ as s) => s end.

			Definition second_key (kvkv : two_keys_values_t)
				:= key (second (kvkv)).

			Definition second_value (kvkv : two_keys_values_t)
				:= value (second (kvkv)).
		End KV.

		Module SN.
			Definition left (s : singleton_node_t) :=
				match s with s_node (_ as L) (_) (_) => L end.

			Definition keyval (s : singleton_node_t) :=
				match s with s_node (_) (_ as kv) (_) => kv end.

			Definition key (s : singleton_node_t) := KV.key (keyval s).
			Definition value (s : singleton_node_t) := KV.value (keyval s).

			Definition right (s : singleton_node_t) :=
				match s with s_node (_) (_) (_ as R) => R end.
		End SN.

		Module DN.
			Definition left (d : doubleton_node_t) :=
				match d with d_node (_ as L) (_) (_) (_) (_) => L end.

			Definition first (d : doubleton_node_t) :=
				match d with d_node (_) (_ as kv) (_) (_) (_) => kv end.

			Definition first_key (d : doubleton_node_t) := KV.key (first (d)).
			Definition first_value (d : doubleton_node_t) := KV.value (first (d)).

			Definition middle (d : doubleton_node_t) :=
				match d with d_node (_) (_) (_ as m) (_) (_) => m end.

			Definition second (d : doubleton_node_t) :=
				match d with d_node (_) (_) (_) (_ as kv) (_) => kv end.

			Definition second_key (d : doubleton_node_t) := KV.key (second (d)).
			Definition second_value (d : doubleton_node_t) := KV.value (second (d)).

			Definition right (d : doubleton_node_t) :=
				match d with d_node (_) (_) (_) (_) (_ as R) => R end.
		End DN.

		Definition value (k : Keys.t) (tr : tree_t)
			: option (Values.t)
			:= let fix value_node (k : Keys.t)
					(node : node_t) : option (Values.t)
				:= (match node
					with singleton_leaf (_ as kv) =>
						(match Keys.ltb (k) (KV.key (kv)),
							Keys.ltb (KV.key (kv)) (k)
						with true, _ => None
						| false, false => Some (KV.value (kv))
						| _, true => None
						end)
					| doubleton_leaf (_ as kvkv) =>
						(match Keys.ltb (k) (KV.first_key (kvkv)),
							Keys.ltb (KV.first_key (kvkv)) (k),
							Keys.ltb (k) (KV.second_key (kvkv)),
							Keys.ltb (KV.second_key (kvkv)) (k)
						with true, _, _, _ => None
						| false, false, _, _ => Some (KV.first_value (kvkv))
						| _, true, true, _ => None
						| _, _, false, false => Some (KV.second_value (kvkv))
						| _, _, _, true => None
						end)
					| singleton_node (_ as sn) =>
						(match Keys.ltb (k) (SN.key (sn)),
							Keys.ltb (SN.key (sn)) (k)
						with true, _ => value_node (k) (SN.left (sn))
						| false, false => Some (SN.value (sn))
						| _, true => value_node (k) (SN.right (sn))
						end)
					| doubleton_node (_ as dn) =>
						(match Keys.ltb (k) (DN.first_key (dn)),
							Keys.ltb (DN.first_key (dn)) (k),
							Keys.ltb (k) (DN.second_key (dn)),
							Keys.ltb (DN.second_key (dn)) (k)
						with true, _, _, _ => value_node (k) (DN.left (dn))
						| false, false, _, _ => Some (DN.first_value (dn))
						| _, true, true, _ => value_node (k) (DN.middle (dn))
						| _, _, false, false => Some (DN.second_value (dn))
						| _, _, _, true => value_node (k) (DN.right (dn))
						end)
				end)
			in (match tr
				with empty_tree => None
				| singleton_tree (_ as kv) =>
					(match Keys.ltb (k) (KV.key (kv)),
						Keys.ltb (KV.key (kv)) (k)
					with true, _ => None
					| false, false => Some (KV.value (kv))
					| _, true => None
					end)
				| doubleton_tree (_ as kvkv) =>
					(match Keys.ltb (k) (KV.first_key (kvkv)),
						Keys.ltb (KV.first_key (kvkv)) (k),
						Keys.ltb (k) (KV.second_key (kvkv)),
						Keys.ltb (KV.second_key (kvkv)) (k)
					with true, _, _, _ => None
					| false, false, _, _ => Some (KV.first_value (kvkv))
					| _, true, true, _ => None
					| _, _, false, false => Some (KV.second_value (kvkv))
					| _, _, _, true => None
					end)
				| singleton_root (_ as sn) =>
					(match Keys.ltb (k) (SN.key (sn)),
						Keys.ltb (SN.key (sn)) (k)
					with true, _ => value_node (k) (SN.left (sn))
					| false, false => Some (SN.value (sn))
					| _, true => value_node (k) (SN.right (sn))
					end)
				| doubleton_root (_ as dn) =>
					(match Keys.ltb (k) (DN.first_key (dn)),
						Keys.ltb (DN.first_key (dn)) (k),
						Keys.ltb (k) (DN.second_key (dn)),
						Keys.ltb (DN.second_key (dn)) (k)
					with true, _, _, _ => value_node (k) (DN.left (dn))
					| false, false, _, _ => Some (DN.first_value (dn))
					| _, true, true, _ => value_node (k) (DN.middle (dn))
					| _, _, false, false => Some (DN.second_value (dn))
					| _, _, _, true => value_node (k) (DN.right (dn))
					end)
			end).

		Definition Test1 (tr : tree_t)
			: tree_t
			:= match tr
				with empty_tree => empty_tree
				| singleton_tree (_) => tr
				| doubleton_tree (_) => tr
				| singleton_root (_) => tr
				| doubleton_root (_) => tr
				end.

	End Trees.
End TwoThreeTrees.
