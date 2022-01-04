Require Coq.Structures.Orders.
Require Coq.Structures.Equalities.

Module TwoThreeTrees.

	Module Trees
		(Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: Coq.Structures.Equalities.Typ.

		Definition key_value_t :=
			Coq.Init.Datatypes.prod (Keys.t) (Values.t).

		Inductive tree_t :=
			empty_tree : tree_t
			| singleton_tree (kv : key_value_t) : tree_t
			| doubleton_tree : doubleton_leaf_t -> tree_t
			| singleton_root : singleton_node_t -> tree_t
			| doubleton_root : doubleton_node_t -> tree_t
		with node_t :=
			singleton_node : singleton_node_t -> node_t
			| doubleton_node : doubleton_node_t -> node_t
			| singleton_leaf (kv : key_value_t) : node_t
			| doubleton_leaf : doubleton_leaf_t -> node_t
		with singleton_node_t :=
			singleton_node_v : node_t
				-> Keys.t -> Values.t
				-> node_t -> singleton_node_t
		with doubleton_node_t :=
			doubleton_node_v : node_t
				-> Keys.t -> Values.t
				-> node_t
				-> Keys.t -> Values.t
				-> node_t -> doubleton_node_t
		with doubleton_leaf_t :=
			doubleton_leaf_v : Keys.t -> Values.t
				-> Keys.t -> Values.t
				-> doubleton_leaf_t.

		Fixpoint left_sn (sn : singleton_node_t)
			: node_t
			:= match sn
			with singleton_node_v (_ as left) (_) (_) (_)
			=> left
			end.

		Fixpoint key_sn (sn : singleton_node_t)
			: Keys.t
			:= match sn
			with singleton_node_v (_) (_ as key) (_) (_)
			=> key
			end.

		Fixpoint value_sn (sn : singleton_node_t)
			: Values.t
			:= match sn
			with singleton_node_v (_) (_) (_ as value) (_)
			=> value
			end.

		Fixpoint right_sn (sn : singleton_node_t)
			: node_t
			:= match sn
			with singleton_node_v (_) (_) (_) (_ as right)
			=> right
			end.

		Fixpoint left_dn (dn : doubleton_node_t)
			: node_t
			:= match dn
			with doubleton_node_v
				(_ as left) (_) (_) (_) (_) (_) (_)
			=> left
			end.

		Fixpoint first_key_dn (dn : doubleton_node_t)
			: Keys.t
			:= match dn
			with doubleton_node_v
				(_) (_ as key) (_) (_) (_) (_) (_)
			=> key
			end.

		Fixpoint first_value_dn (dn : doubleton_node_t)
			: Values.t
			:= match dn
			with doubleton_node_v
				(_) (_) (_ as value) (_) (_) (_) (_)
			=> value
			end.

		Fixpoint middle_dn (dn : doubleton_node_t)
			: node_t
			:= match dn
			with doubleton_node_v
				(_) (_) (_) (_ as middle) (_) (_) (_)
			=> middle
			end.

		Fixpoint second_key_dn (dn : doubleton_node_t)
			: Keys.t
			:= match dn
			with doubleton_node_v
				(_) (_) (_) (_) (_ as key) (_) (_)
			=> key
			end.

		Fixpoint second_value_dn (dn : doubleton_node_t)
			: Values.t
			:= match dn
			with doubleton_node_v
				(_) (_) (_) (_) (_) (_ as value) (_)
			=> value
			end.

		Fixpoint right_dn (dn : doubleton_node_t)
			: node_t
			:= match dn
			with doubleton_node_v
				(_) (_) (_) (_) (_) (_) (_ as right)
			=> right
			end.

		Fixpoint first_key_dl (dl : doubleton_leaf_t)
			: Keys.t
			:= match dl
			with doubleton_leaf_v (_ as key) (_) (_) (_)
			=> key
			end.

		Fixpoint first_value_dl (dl : doubleton_leaf_t)
			: Values.t
			:= match dl
			with doubleton_leaf_v (_) (_ as value) (_) (_)
			=> value
			end.

		Fixpoint second_key_dl (dl : doubleton_leaf_t)
			: Keys.t
			:= match dl
			with doubleton_leaf_v (_) (_) (_ as key) (_)
			=> key
			end.

		Fixpoint second_value_dl (dl : doubleton_leaf_t)
			: Values.t
			:= match dl
			with doubleton_leaf_v (_) (_) (_) (_ as value)
			=> value
			end.

		Definition t := tree_t.

		Fixpoint value_node (k : Keys.t) (node : node_t)
			: Coq.Init.Datatypes.option (Values.t)
			:= match node
			with singleton_leaf (_ as kv)
			=> match Keys.ltb (k) (fst (kv)),
				Keys.ltb (fst (kv)) (k)
				with true, _ => None
				| false, false => Some (snd (kv))
				| _, true => None
				end
			| doubleton_leaf (_ as dl)
			=> match Keys.ltb (k) (first_key_dl (dl))
				with true
				=> Coq.Init.Datatypes.None
				| false
				=> match Keys.ltb (first_key_dl (dl)) (k)
					with false
					=> Coq.Init.Datatypes.Some
						(first_value_dl (dl))
					| true
					=> match Keys.ltb (k) (second_key_dl (dl))
						with true
						=> Coq.Init.Datatypes.None
						| false
						=> match Keys.ltb (second_key_dl (dl)) (k)
							with false
							=> Coq.Init.Datatypes.Some
								(second_value_dl (dl))
							| true
							=> Coq.Init.Datatypes.None
							end
						end
					end
				end
			| singleton_node (_ as sn)
			=> match Keys.ltb (k) (key_sn (sn))
				with true
				=> value_node (k) (left_sn (sn))
				| false
				=> match Keys.ltb (key_sn (sn)) (k)
					with false
					=> Coq.Init.Datatypes.Some
						(value_sn (sn))
					| true
					=> value_node (k) (right_sn (sn))
					end
				end
			| doubleton_node (_ as dn)
			=> match Keys.ltb (k) (first_key_dn (dn))
				with true
				=> value_node (k) (left_dn (dn))
				| false
				=> match Keys.ltb (first_key_dn (dn)) (k)
					with false
					=> Coq.Init.Datatypes.Some
						(first_value_dn (dn))
					| true
					=> match Keys.ltb (k) (second_key_dn (dn))
						with true
						=> value_node (k) (middle_dn (dn))
						| false
						=> match Keys.ltb (second_key_dn (dn)) (k)
							with false
							=> Coq.Init.Datatypes.Some
								(second_value_dn (dn))
							| true
							=> value_node (k) (right_dn (dn))
							end
						end
					end
				end
			end.

		Definition value (k : Keys.t) (tr : tree_t)
			: Coq.Init.Datatypes.option (Values.t)
			:= match tr
			with empty_tree => Coq.Init.Datatypes.None
			| singleton_tree (_ as kv)
			=> match Keys.ltb (k) (fst (kv)),
				Keys.ltb (fst (kv)) (k)
				with true, _ => None
				| false, false => Some (snd (kv))
				| _, true => None
				end
			| doubleton_tree (_ as dl)
			=> match Keys.ltb (k) (first_key_dl (dl))
				with true
				=> Coq.Init.Datatypes.None
				| false
				=> match Keys.ltb (first_key_dl (dl)) (k)
					with false
					=> Coq.Init.Datatypes.Some
						(first_value_dl (dl))
					| true
					=> match Keys.ltb (k) (second_key_dl (dl))
						with true
						=> Coq.Init.Datatypes.None
						| false
						=> match Keys.ltb (second_key_dl (dl)) (k)
							with false
							=> Coq.Init.Datatypes.Some
								(second_value_dl (dl))
							| true
							=> Coq.Init.Datatypes.None
							end
						end
					end
				end
			| singleton_root (_ as sn)
			=> match Keys.ltb (k) (key_sn (sn))
				with true
				=> value_node (k) (left_sn (sn))
				| false
				=> match Keys.ltb (key_sn (sn)) (k)
					with false
					=> Coq.Init.Datatypes.Some
						(value_sn (sn))
					| true
					=> value_node (k) (right_sn (sn))
					end
				end
			| doubleton_root (_ as dn)
			=> match Keys.ltb (k) (first_key_dn (dn))
				with true
				=> value_node (k) (left_dn (dn))
				| false
				=> match Keys.ltb (first_key_dn (dn)) (k)
					with false
					=> Coq.Init.Datatypes.Some
						(first_value_dn (dn))
					| true
					=> match Keys.ltb (k) (second_key_dn (dn))
						with true
						=> value_node (k) (middle_dn (dn))
						| false
						=> match Keys.ltb (second_key_dn (dn)) (k)
							with false
							=> Coq.Init.Datatypes.Some
								(second_value_dn (dn))
							| true
							=> value_node (k) (right_dn (dn))
							end
						end
					end
				end
			end.


    End Trees.
End TwoThreeTrees.
