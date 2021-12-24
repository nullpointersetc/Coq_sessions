Require Coq.Structures.Equalities.
Require Coq.Structures.Orders.

Module TwoThreeTrees
	(Keys : Coq.Structures.Orders.LtBool)
	(Values : Coq.Structures.Equalities.Typ).

	Inductive tree_t : Type
		:= empty_tree
			: tree_t
		|  single_two
			: Keys.t -> Values.t -> tree_t
		|  single_three
			: Keys.t -> Values.t
			-> Keys.t -> Values.t -> tree_t
		|  root_two
			: node_t -> Keys.t -> Values.t
			-> node_t -> tree_t
		|  root_three
			: node_t -> Keys.t -> Values.t
			-> node_t -> Keys.t -> Values.t
			-> node_t -> tree_t
		with node_t : Type
		:= leaf_two
			: Keys.t -> Values.t -> node_t
		|  leaf_three
			: Keys.t -> Values.t
			-> Keys.t -> Values.t -> node_t
		|  node_two
			: node_t -> Keys.t -> Values.t
			-> node_t -> node_t
		|  node_three
			: node_t -> Keys.t -> Values.t
			-> node_t -> Keys.t -> Values.t
			-> node_t -> node_t.

	Definition t := tree_t.

	Definition empty := empty_tree.

End TwoThreeTrees.


