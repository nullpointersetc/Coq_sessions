Require Coq.Structures.Orders.
Require Coq.Structures.Equalities.

Module TwoThreeTrees.

	Module Trees
		(Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: Coq.Structures.Equalities.Typ.

		Import Coq.Init.Datatypes.

		Inductive tree_t :=
			empty_tree : tree_t
			| singleton_tree (kv : key_value_t) : tree_t
			| doubleton_tree (first: key_value_t)
				(second: key_value_t) : tree_t
			| singleton_root (left : node_t)
				(kv : key_value_t) (right : node_t) : tree_t
			| doubleton_root (left : node_t)
				(first : key_value_t) (middle : node_t)
				(second : key_value_t) (right : node_t) : tree_t
		with node_t :=
			singleton_node (left : node_t)
				(kv : key_value_t) (right : node_t) : node_t
			| doubleton_node (left : node_t)
				(first : key_value_t) (middle : node_t)
				(second : key_value_t) (right : node_t) : node_t
			| singleton_leaf (kv : key_value_t) : node_t
			| doubleton_leaf (first : key_value_t)
				(second : key_value_t) : node_t
		with key_value_t :=
			kv_pair (key : Keys.t) (value : Values.t) : key_value_t.

		Definition t := tree_t.

		Definition value (k : Keys.t) (tr : tree_t)
			: Coq.Init.Datatypes.option (Values.t)
			:= let fix value_node (k : Keys.t)
					(node : node_t) : Coq.Init.Datatypes.option (Values.t)
				:= (match node
					with singleton_leaf (kv_pair (_ as key) (_ as value)) =>
						(match Keys.ltb (k) (key),
							Keys.ltb (key) (k)
						with true, _ => Coq.Init.Datatypes.None
						| false, false => Coq.Init.Datatypes.Some (value)
						| _, true => Coq.Init.Datatypes.None
						end)
					| doubleton_leaf
							(kv_pair (_ as first_key) (_ as first_value))
							(kv_pair (_ as second_key) (_ as second_value)) =>
						(match Keys.ltb (k) (first_key),
							Keys.ltb (first_key) (k),
							Keys.ltb (k) (second_key),
							Keys.ltb (second_key) (k)
						with true, _, _, _ => Coq.Init.Datatypes.None
						| false, false, _, _ =>
							Coq.Init.Datatypes.Some (first_value)
						| _, true, true, _ => Coq.Init.Datatypes.None
						| _, _, false, false =>
							Coq.Init.Datatypes.Some (second_value)
						| _, _, _, true => Coq.Init.Datatypes.None
						end)
					| singleton_node (_ as left)
							(kv_pair (_ as key) (_ as value))
							(_ as right) =>
						(match Keys.ltb (k) (key), Keys.ltb (key) (k)
						with true, _ => value_node (k) (left)
						| false, false => Coq.Init.Datatypes.Some (value)
						| _, true => value_node (k) (right)
						end)
					| doubleton_node (_ as left)
							(kv_pair (_ as first_key) (_ as first_value))
							(_ as middle)
							(kv_pair (_ as second_key) (_ as second_value))
							(_ as right) =>
						(match Keys.ltb (k) (first_key),
							Keys.ltb (first_key) (k),
							Keys.ltb (k) (second_key),
							Keys.ltb (second_key) (k)
						with true, _, _, _ => value_node (k) (left)
						| false, false, _, _ =>
							Coq.Init.Datatypes.Some (first_value)
						| _, true, true, _ => value_node (k) (middle)
						| _, _, false, false =>
							Coq.Init.Datatypes.Some (second_value)
						| _, _, _, true => value_node (k) (right)
						end)
				end)
			in (match tr
				with empty_tree => Coq.Init.Datatypes.None
				| singleton_tree (kv_pair (_ as key) (_ as value)) =>
					(match Keys.ltb (k) (key),
						Keys.ltb (key) (k)
					with true, _ => Coq.Init.Datatypes.None
					| false, false => Coq.Init.Datatypes.Some (value)
					| _, true => Coq.Init.Datatypes.None
					end)
				| doubleton_tree
						(kv_pair (_ as first_key) (_ as first_value))
						(kv_pair (_ as second_key) (_ as second_value)) =>
					(match Keys.ltb (k) (first_key),
						Keys.ltb (first_key) (k),
						Keys.ltb (k) (second_key),
						Keys.ltb (second_key) (k)
					with true, _, _, _ =>
						Coq.Init.Datatypes.None
					| false, false, _, _ =>
						Coq.Init.Datatypes.Some (first_value)
					| _, true, true, _ =>
						Coq.Init.Datatypes.None
					| _, _, false, false =>
						Coq.Init.Datatypes.Some (second_value)
					| _, _, _, true =>
						Coq.Init.Datatypes.None
					end)
				| singleton_root (_ as left)
						(kv_pair (_ as key) (_ as value))
						(_ as right) =>
					(match Keys.ltb (k) (key),
						Keys.ltb (key) (k)
					with true, _ => value_node (k) (left)
					| false, false => Coq.Init.Datatypes.Some (value)
					| _, true => value_node (k) (right)
					end)
				| doubleton_root (_ as left)
						(kv_pair (_ as first_key) (_ as first_value))
						(_ as middle)
						(kv_pair (_ as second_key) (_ as second_value))
						(_ as right) =>
					(match Keys.ltb (k) (first_key),
						Keys.ltb (first_key) (k),
						Keys.ltb (k) (second_key),
						Keys.ltb (second_key) (k)
					with true, _, _, _ =>
						value_node (k) (left)
					| false, false, _, _ =>
						Coq.Init.Datatypes.Some (first_value)
					| _, true, true, _ =>
						value_node (k) (middle)
					| _, _, false, false =>
						Coq.Init.Datatypes.Some (second_value)
					| _, _, _, true =>
						value_node (k) (right)
					end)
			end).

    End Trees.
End TwoThreeTrees.
