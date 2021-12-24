Require Coq.Structures.Equalities.
Require Coq.Structures.Orders.

Module TwoThreeTrees.
	Module Trees
		(Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: Coq.Structures.Equalities.Typ.

		Inductive node_t : Type
			:= binary_node
				: node_t
				-> Keys.t -> Values.t
				-> node_t -> node_t
			| ternary_node
				: node_t
				-> Keys.t -> Values.t
				-> node_t
				-> Keys.t -> Values.t
				-> node_t -> node_t
			| singleton_leaf
				: Keys.t -> Values.t -> node_t
			| doubleton_leaf
				: Keys.t -> Values.t
				-> Keys.t -> Values.t -> node_t.

		Inductive tree_t : Type
			:= empty_tree
				: tree_t
			| singleton_tree
				: Keys.t -> Values.t -> tree_t
			| doubleton_tree
				: Keys.t -> Values.t
				-> Keys.t -> Values.t -> tree_t
			| binary_root
				: node_t -> Keys.t -> Values.t
				-> node_t -> tree_t
			| ternary_root
				: node_t -> Keys.t -> Values.t
				-> node_t -> Keys.t -> Values.t
				-> node_t -> tree_t.

		Definition t := tree_t.

		Definition empty := empty_tree.

		Fixpoint insert (k : Keys.t)
			(v : Values.t)
			(t : tree_t)
			: tree_t
			:= match t
			with empty_tree
				=> singleton_tree (k) (v)
			| singleton_tree (k1) (v1)
				=> match Keys.ltb(k)(k1)
				with true => doubleton_tree (k) (v) (k1) (v1)
				| false => match Keys.ltb(k1)(k)
				with true => doubleton_tree (k1) (v1) (k) (v)
				| false => singleton_tree (k) (v)
				end end.
			| doubleton_tree (k1) (v1) (k2) (v2)
				=> binary_root
					(singleton_leaf k1 v1)
					(k) (v)
					(singleton_leaf k2 v2)
			| binary_root (ln) (k1) (v1) (rn)
				=> empty_tree
			| ternary_root (ln) (k1) (v1) (mn) (k2) (v2) (rn)
				=> empty_tree
			end.

	End Trees.

End TwoThreeTrees.


