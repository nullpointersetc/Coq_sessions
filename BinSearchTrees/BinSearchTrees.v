Require Coq.Structures.Equalities.
Require Coq.Structures.Orders.
Module BinSearchTrees.

	Module Type ITrees
		(Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ).

		Parameter t : Type.
		Parameter empty : t.
		Parameter singleton : Keys.t -> Values.t -> t.
		Parameter insert : Keys.t -> Values.t -> t -> t.
		Parameter contains_key : Keys.t -> t -> bool.
		Parameter value_for : Keys.t -> t -> option (Values.t).
		Parameter remove_key : Keys.t -> t -> t.
	End ITrees.

	Module Trees
		(Keys : Coq.Structures.Orders.LtBool)
		(Values : Coq.Structures.Equalities.Typ)
		<: ITrees (Keys) (Values).

		Inductive tree_t : Type
			:= empty_tree : tree_t
			|  tree_node : tree_t -> Keys.t ->
				Values.t -> tree_t -> tree_t.

		Definition t := tree_t.

		Definition empty := empty_tree.

		Definition singleton
			(key1 : Keys.t)
			(value1 : Values.t)
			: tree_t
			:= tree_node (empty_tree) (key1)
				(value1) (empty_tree).

		Fixpoint insert (key1 : Keys.t)
			(value1 : Values.t)
			(tree2 : tree_t) : tree_t
		:= match tree2
		with empty_tree
			=> tree_node (empty_tree) (key1)
				(value1) (empty_tree)
		| tree_node (left2) (key2) (value2) (right2)
			=> if Keys.ltb (key1) (key2)
			then tree_node (insert (key1) (value1) (left2))
				(key2) (value2) (right2)
			else if Keys.ltb (key2) (key1)
			then tree_node (left2) (key2) (value2)
				(insert (key1) (value1) (right2))
			else tree_node (left2) (key1) (value1) (right2)
		end.

		Fixpoint contains_key (key1 : Keys.t)
			(tree2 : tree_t) : bool
		:= match tree2
		with empty_tree
			=> false
		| tree_node (left2)(key2)(value2)(right2)
			=> if Keys.ltb (key1)(key2)
			then contains_key (key1)(left2)
			else if Keys.ltb (key2)(key1)
			then contains_key (key1)(right2)
			else true
		end.

		Fixpoint value_for (key1 : Keys.t)
			(tree2 : tree_t) : option (Values.t)
		:= match tree2
		with empty_tree
			=> None
		| tree_node (left2) (key2) (value2) (right2)
			=> if Keys.ltb (key1) (key2)
			then value_for (key1) (left2)
			else if Keys.ltb (key2) (key1)
			then value_for (key1) (right2)
			else Some (value2)
		end.

		Fixpoint remove_key (key1 : Keys.t)
			(tree2 : tree_t)
			: tree_t
		:= 
		match tree2 return tree_t
		with empty_tree
			=> tree2
		| tree_node (left2) (key2) (value2) (right2)
			=> match (Keys.ltb (key1) (key2))
			with true
			=> tree_node (remove_key (key1) (left2))
				(key2) (value2) (right2)
			| false
			=> match (Keys.ltb (key2) (key1))
			with true
			=> tree_node (left2) (key2) (value2)
				(remove_key (key1) (right2))
			| false
			=> match (right2)
			with empty_tree => left2
			| tree_node (left3) (key3) (value3) (right3) =>
				tree_node (left2) (key3) (value3)
					(remove_key (key3) (right2))
			end
			end
			end
		end.

		Proposition Prop1 :
			forall key1 : Keys.t,
			eq (false) (contains_key (key1) (empty_tree)).
		Proof.
			reflexivity.
		Qed.

	End Trees.

	Module TreesNat
       		:= Trees (Coq.Init.Nat) (Coq.Init.Nat).

	Module ValidateTreesNat.
		Definition TreeNat := TreesNat.t.
		Definition EmptyNat := TreesNat.empty.
		Definition singleton := TreesNat.singleton.
		Definition contains_key := TreesNat.contains_key.
		Definition value_for := TreesNat.value_for.
 
		Definition Tree1 := singleton (1) (10).

		Proposition Prop1 :
			contains_key (1) (EmptyNat) = false.
		Proof.
			reflexivity.
		Qed.

		Proposition Prop2 :
			TreesNat.contains_key (1)
			(TreesNat.singleton (1)(10)) = true.
		Proof.
			reflexivity.
		Qed.

		(*
		Proposition Prop2a :
			forall n : nat, forall v : nat,
			TreesNat.contains_key (n)
			(TreesNat.singleton (n) (v)) = true.
		Proof.
			reflexivity.
		Qed.
		*)

		Proposition Prop3 :
			contains_key (2) (Tree1) = false.
		Proof.
			reflexivity.
		Qed.

		Proposition Prop4 :
			value_for (1) (Tree1) = Some (10).
		Proof.
			reflexivity.
		Qed.

		Proposition Prop5 :
			value_for (2) (Tree1) = None.
		Proof.
			reflexivity.
		Qed.

	End ValidateTreesNat.

End BinSearchTrees.


