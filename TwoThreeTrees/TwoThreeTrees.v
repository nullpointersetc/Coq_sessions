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

		Definition insert (k : Keys.t)
			(v : Values.t)
			(t : tree_t)
			: tree_t
			:= match t
			with empty_tree
			=> singleton_tree (k) (v)
			| singleton_tree (k1) (v1)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> doubleton_tree (k) (v) (k1) (v1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.true
				=> doubleton_tree (k1) (v1) (k) (v)
				| Coq.Init.Datatypes.false
				=> singleton_tree (k) (v)
				end end
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

		Fixpoint node_contains (k : Keys.t)
			(n : node_t)
			: Coq.Init.Datatypes.bool
			:= match n
			with binary_node (_ as n1)
				(_ as k2) (_) (_ as n3)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> node_contains(k)(n3)
				end end
			| ternary_node (_ as n1)
				(_ as k2) (_) (_ as n3)
				(_ as k4) (_) (_ as n5)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k4)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n3)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k4)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> node_contains(k)(n5)
				end end end end
			| singleton_leaf (_ as k1) (_)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				end end
			| doubleton_leaf
				(_ as k1) (_) (_ as k2) (_)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				end end end end
			end.

		Definition contains (k : Keys.t)
			(t : tree_t)
			: Coq.Init.Datatypes.bool
			:= match t
			with empty_tree
			=> Coq.Init.Datatypes.false
			| singleton_tree (_ as k1) (_)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				end end
			| doubleton_tree (_ as k1) (_)
				(_ as k2) (_)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.false
				end end end end
			| binary_root (_ as n1)
				(_ as k2) (_) (_ as n3)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n3)
				| Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				end end
			| ternary_root (_ as n1)
				(_ as k2) (_) (_ as n3)
				(_ as k4) (_) (_ as n5)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k4)
				with Coq.Init.Datatypes.true
				=> node_contains(k)(n3)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k4)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.true
				| Coq.Init.Datatypes.true
				=> node_contains(k)(n5)
				end end end end
			end.

		Fixpoint node_value_at (k : Keys.t)
			(n : node_t)
			: Coq.Init.Datatypes.option(Values.t)
			:= match n
			with binary_node (_ as n1)
				(_ as k2) (_ as v2) (_ as n3)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v2)
				| Coq.Init.Datatypes.true
				=> node_value_at(k)(n3)
				end end
			| ternary_node (_ as n1)
				(_ as k2) (_ as v2) (_ as n3)
				(_ as k4) (_ as v4) (_ as n5)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v2)
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k4)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n3)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k4)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v4)
				| Coq.Init.Datatypes.true
				=> node_value_at(k)(n5)
				end end end end
			| singleton_leaf (_ as k1) (_ as v1)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v1)
				| Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				end end
			| doubleton_leaf (_ as k1) (_ as v1)
				(_ as k2) (_ as v2)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v1)
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v2)
				| Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				end end end end
			end.

		Definition value_at (k : Keys.t)
			(t : tree_t)
			: Coq.Init.Datatypes.option(Values.t)
			:= match t
			return Coq.Init.Datatypes.option(Values.t)
			with empty_tree
			=> Coq.Init.Datatypes.None
			| singleton_tree (_ as k1) (_ as v1)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v1)
				end end
			| doubleton_tree (_ as k1) (_ as v1)
				(_ as k2) (_ as v2)
			=> match Keys.ltb(k)(k1)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k1)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v1)
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v2)
				| Coq.Init.Datatypes.true
				=> Coq.Init.Datatypes.None
				end end end end
			| binary_root (_ as n1)
				(_ as k2) (_ as v2) (_ as n3)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n3)
				| Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v2)
				end end
			| ternary_root (_ as n1)
				(_ as k2) (_ as v2) (_ as n3)
				(_ as k4) (_ as v4) (_ as n5)
			=> match Keys.ltb(k)(k2)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n1)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k2)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v2)
				| Coq.Init.Datatypes.true
				=> match Keys.ltb(k)(k4)
				with Coq.Init.Datatypes.true
				=> node_value_at(k)(n3)
				| Coq.Init.Datatypes.false
				=> match Keys.ltb(k4)(k)
				with Coq.Init.Datatypes.false
				=> Coq.Init.Datatypes.Some(v4)
				| Coq.Init.Datatypes.true
				=> node_value_at(k)(n5)
				end end end end
			end.

	End Trees.

End TwoThreeTrees.


