Module BinSearchTrees.
	(* Sat Jun 26 20:24:44 EDT 2021 *)

	Inductive Tree (Key : Set)
		(Less : Key -> Key -> bool)
		(Value : Set) : Set
	:=  Empty : Tree (Key) (Less) (Value)
	|   Node  : Tree (Key) (Less) (Value)
                -> Key
		-> Value
		-> Tree (Key) (Less) (Value)
                -> Tree (Key) (Less) (Value).

	Definition Singleton (Key : Set)
		(Less : Key -> Key -> bool)
		(Value : Set)
		(key1 : Key)
		(value1 : Value)
		: Tree (Key) (Less) (Value)
	:= Node (Key) (Less) (Value)
		(Empty (Key) (Less) (Value))
		(key1) (value1)
		(Empty (Key) (Less) (Value)).

	Fixpoint Insert {Key : Set}
		{Less : Key -> Key -> bool}
		{Value : Set}
		(key1 : Key)
		(value1 : Value)
		(tree2 : Tree (Key) (Less) (Value))
		: Tree (Key) (Less) (Value)
	:= match tree2
	with Empty(_)(_)(_)
		 => Node (Key) (Less) (Value)
			(Empty (Key) (Less) (Value))
			(key1) (value1)
			(Empty (Key) (Less) (Value))
	| Node (_)(_)(_) (left2) (key2) (value2) (right2)
		=> if Less (key1) (key2)
		then Node (Key) (Less) (Value)
			(Insert (key1) (value1) (left2))
			(key2) (value2) (right2)
		else if Less (key2) (key1)
		then Node (Key) (Less) (Value)
			(left2) (key2) (value2)
			(Insert (key1) (value1) (right2))
		else Node (Key) (Less) (Value)
			(left2) (key1) (value1) (right2)
	end.

	Fixpoint Contains_Key {Key : Set}
		{Less : Key -> Key -> bool}
		{Value : Set}
		(key1 : Key)
		(tree2 : Tree (Key) (Less) (Value))
		: bool
	:= match tree2
	with Empty(_)(_)(_)
		=> false
	| Node (_)(_)(_) (left2) (key2) (value2) (right2)
		=> if Less (key1) (key2)
		then Contains_Key (key1) (left2)
		else if Less (key2) (key1)
		then Contains_Key (key1) (right2)
		else true
	end.

	Fixpoint Value_For {Key : Set}
		{Less : Key -> Key -> bool}
		{Value : Set}
		(key1 : Key)
		(tree2 : Tree (Key) (Less) (Value))
		: option (Value)
	:= match tree2
	with Empty(_)(_)(_)
		=> None
	| Node (_)(_)(_) (left2) (key2) (value2) (right2)
		=> if Less (key1) (key2)
		then Value_For (key1) (left2)
		else if Less (key2) (key1)
		then Value_For (key1) (right2)
		else Some (value2)
	end.

	Fixpoint Remove_Key {Key : Set}
		{Less : Key -> Key -> bool}
		{Value : Set}
		(key1 : Key)
		(tree2 : Tree (Key) (Less) (Value))
		: Tree (Key) (Less) (Value)
	:= 
	match tree2
	with Empty(_)(_)(_)
		=> tree2
	| Node(_)(_)(_) (left2) (key2) (value2) (right2)
		=> if (Less (key1) (key2))
		then  Node (Key) (Less) (Value)
			(Remove_Key (key1) (left2))
			(key2) (value2) (right2)
		else if (Less (key2) (key1))
		then Node (Key) (Less) (Value)
			(left2) (key2) (value2)
			(Remove_Key (key1) (right2))
		else match right2
		with Empty (_)(_)(_)
			=> left2
		| Node(_)(_)(_) (left3) (key3) (value3) (right3)
			=> Node (Key) (Less) (Value)
				(left2) (key3) (value3)
				(Remove_Key (key3) (right3))
		end
	end.

End BinSearchTrees.

Module BinSearchTrees_Tests.

	Definition Tree_Nat := BinSearchTrees.Tree
			(nat) (Nat.ltb) (nat).

	Definition Empty_Nat := BinSearchTrees.Empty
			(nat) (Nat.ltb) (nat).

	Definition Node_Nat := BinSearchTrees.Node
			(nat) (Nat.ltb) (nat).

	Definition Singleton_Nat :=
		BinSearchTrees.Singleton
			(nat) (Nat.ltb) (nat).
 
	Definition Contains_Nat_Key :=
		BinSearchTrees.Contains_Key
			(Key:=nat) (Less:=Nat.ltb) (Value:=nat).

	Definition Nat_Value_For :=
		BinSearchTrees.Value_For
			(Key:=nat) (Less:=Nat.ltb) (Value:=nat).

	Definition tree1 := Singleton_Nat (1) (10).

	Proposition Prop1 :
		eq false (Contains_Nat_Key (1) (Empty_Nat)).
	Proof.
		reflexivity.
	Qed.

	Proposition Prop2 :
		eq true (Contains_Nat_Key (1) (tree1)).
	Proof.
		reflexivity.
	Qed.

	Proposition Prop3 :
		eq false (Contains_Nat_Key (2) (tree1)).
	Proof.
		reflexivity.
	Qed.

	Proposition Prop4 :
		eq (Some 10) (Nat_Value_For (1) (tree1)).
	Proof.
		reflexivity.
	Qed.

	Proposition Prop5 :
		eq (None) (BinSearchTrees.Value_For (2) (tree1)).
	Proof.
		reflexivity.
	Qed.

	Definition tree2 := BinSearchTrees.Insert (5) (25) (tree1).

	Proposition Prop6 :
		eq tree2 (Node_Nat (Empty_Nat) (1) (10)
			(Node_Nat (Empty_Nat) (5) (25) (Empty_Nat))).
	Proof.
		reflexivity.
	Qed.

End BinSearchTrees_Tests.


