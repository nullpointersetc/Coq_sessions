Module BinSearchTrees.

	Module Type KeyModType.
		Parameter t : Set.
		Parameter ltb : t -> t -> bool.
	End KeyModType.

	Module Type ValueModType.
		Parameter t : Set.
	End ValueModType.

	Module Trees (Keys : KeyModType) (Values : ValueModType).

		Inductive t : Set
			:= Empty : t
			|  Node : t -> Keys.t ->
				Values.t -> t -> t.

		Definition Singleton
			(key1 : Keys.t)
			(value1 : Values.t)
			: Trees.t
			:= Node (Empty)(key1)(value1)(Empty).

		Fixpoint Insert (key1 : Keys.t)
			(value1 : Values.t)
			(tree2 : Trees.t) : Trees.t
		:= match tree2
		with Empty
			=> Node(Empty)(key1)(value1)(Empty)
		| Node(left2)(key2)(value2)(right2)
			=> match Keys.ltb(key1)(key2)
			with true =>
				Node (Insert(key1)(value1)(left2))
					(key2)(value2)(right2)
			| false =>
				match Keys.ltb(key2)(key1)
				with true =>
					Node (left2)(key2)(value2)
						(Insert(key1)(value1)(right2))
				| false =>
				Node (left2)(key1)(value1)(right2)
				end
			end
		end.

		Fixpoint Contains_Key (key1 : Keys.t)
			(tree2 : Trees.t) : bool
		:= match tree2
		with Empty
			=> false
		| Node (left2)(key2)(value2)(right2)
			=> match Keys.ltb (key1)(key2)
			with true =>
				Contains_Key (key1)(left2)
			| false =>
				match Keys.ltb (key2)(key1)
				with true =>
					Contains_Key (key1)(right2)
				| false => true
				end
			end
		end.

		Fixpoint Value_For (key1 : Keys.t)
			(tree2 : Trees.t) : option (Values.t)
		:= match tree2
		with Empty
			=> None
		| Node (left2) (key2) (value2) (right2)
			=> match Keys.ltb (key1) (key2)
			with true =>
				Value_For (key1) (left2)
			| false =>
				match Keys.ltb (key2) (key1)
				with true => Value_For (key1) (right2)
				| false => Some (value2)
				end
			end
		end.

		Fixpoint Remove_Key (key1 : Keys.t)
			(tree2 : Trees.t)
			: Trees.t
		:= let fix Reinsert
			(tree3 : Trees.t)
			(tree4 : Trees.t)
			: Trees.t
			:= match tree4
			with Empty => tree3
			| Node (left4) (key4) (value4) (right4)
				=> Node (Reinsert (tree3) (left4))
					(key4) (value4) (right4)
			end
		in let Remove_From_Node
			(left5 : Trees.t) 
			(key5 : Keys.t)
			(value5 : Values.t)
			(right5 : Trees.t)
			: Trees.t
		:= match Keys.ltb (key1) (key5)
		with true =>
			Node (Remove_Key (key1) (left5))
				(key5) (value5) (right5)
		| false =>
			match Keys.ltb (key5) (key1)
			with true =>
				Node (left5) (key5) (value5)
					(Remove_Key (key1) (right5))
			| false => Reinsert (left5) (right5)
			end
		end
		in match tree2
		with Empty => tree2
		| Node (left2) (key2) (value2) (right2)
			=> Remove_From_Node (left2) (key2) (value2) (right2)
		end.

	End Trees.

	Module Trees_Nat := Trees (Coq.Init.Nat) (Coq.Init.Nat).

	Module Validate_Trees_Nat.
		Definition Tree_Nat := Trees_Nat.t.
		Definition Empty_Nat := Trees_Nat.Empty.
		Definition Singleton_Nat := Trees_Nat.Singleton.
		Definition Contains_Key := Trees_Nat.Contains_Key.
		Definition Value_For := Trees_Nat.Value_For.
 
		Definition Tree1 := Singleton_Nat (1) (10).

		Proposition Prop1 :
			Contains_Key (1) (Empty_Nat) = false.
		Proof.
			reflexivity.
		Qed.

		Proposition Prop2 :
			Contains_Key (1) (Tree1) = true.
		Proof.
			reflexivity.
		Qed.

		Proposition Prop3 :
			Contains_Key (2) (Tree1) = false.
		Proof.
			reflexivity.
		Qed.

		Proposition Prop4 :
			Value_For (1) (Tree1) = Some (10).
		Proof.
			reflexivity.
		Qed.

		Proposition Prop5 :
			Value_For (2) (Tree1) = None.
		Proof.
			reflexivity.
		Qed.

	End Validate_Trees_Nat.

End BinSearchTrees.


