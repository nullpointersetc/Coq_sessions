Require Coq.Structures.Equalities.
Require Coq.Structures.Orders.

Module TwoThreeTrees.
	Module Trees
		(Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: Coq.Structures.Equalities.Typ.

		Inductive tree_t : Type
			:= empty_node
				: tree_t
			|  binary_node
				: tree_t
				-> Keys.t -> Values.t
				-> tree_t
				-> tree_t
			|  ternary_node
				: tree_t
				-> Keys.t -> Values.t
				-> tree_t
				-> Keys.t -> Values.t
				-> tree_t
				-> tree_t.

		Definition t := tree_t.

		Definition empty := empty_node.

		Fixpoint insert (k : Keys.t)
			(v : Values.t)
			(t : tree_t)
			: tree_t
			:= (*1*) match t
			with empty_node
			=> binary_node (t) (k) (v) (t)
			| binary_node (_ as t1)
				(_ as k1) (_ as v1) (_ as t2)
			=> (*2*) match Keys.ltb(k)(k1)
				with true
				=> binary_node(insert k v t1)(k1)(v1)(t2)
				| false
				=> (*3*) match Keys.ltb(k1)(k)
				with true
				=> binary_node(t1)(k1)(v1)(insert k v t2)
				| false
				=> binary_node(t1)(k)(v)(t2)
				(*3*) end (*2*) end
			| ternary_node (_ as t1)
				(_ as k1) (_ as v1) (_ as t2)
				(_ as k2) (_ as v2) (_ as t3)
			=> (*4*) match Keys.ltb(k)(k1)
				with true
				=> ternary_node(insert k v t1)
					(k1)(v1)(t2)(k2)(v2)(t3)
				| false
				=> (*5*) match Keys.ltb(k1)(k)
				with true
				=> (*6*) match Keys.ltb(k2)(k)
					with true
					=> ternary_node(t1)(k1)(v1)
						(insert k v t2)(k2)(v2)(t3)
					| false
					=> (*7*) match Keys.ltb(k)(k2)
					with true
					=> ternary_node (t1)(k1)(v1)
						(t2)(k2)(v2)(insert k v t3)
					| false =>
						ternary_node(t1)(k1)(v1)
							(t2)(k)(v)(t3)
					(*7*) end (*6*) end
				| false
				=> ternary_node(t1)(k)(v)(t2)(k2)(v2)(t3)
				(*5*) end (*4*) end
			(*1*) end.

	End Trees.

End TwoThreeTrees.


