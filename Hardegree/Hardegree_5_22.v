(**
*** To use this file: 
******* coqtop -l Hardegree_5_22
*** or
******* coqtop -lv Hardegree_5_22
***
*** This is an example of exercises from Gary Hardegree's textbook,
*** "Symbolic Logic: A First Course" as published at
*** <http://courses.umass.edu/phil110-gmh/MAIN/IHome-5.htm>
*** as of December 8th 2021, done as a Coq session.
*** The exercises are taken from section 5.22 of the textbook.
**)

Require Coq.Logic.Classical_Prop.

Section Hardegree_5_22.

(** Example Exercise_1 is equivalent to this
*** symbolic proof which is mostly in Hardegree's notation.
***
*** (1) P           Pr
*** (2) P → Q       Pr
*** (3) Q → R       Pr
*** (4) R → S       Pr
*** (5) SHOW: S     DD
*** (6) |   Q       2,1,MPP
*** (7) |   R       3,6,MPP
*** (8) |   S       4,7,MPP,QED
***
*** Note: "Pr" indicates a Premise. "DD" indicates Direct Derivation.
*** "MPP" indicates Modus Ponendo Ponens (Hardegree would use →O instead.)
*** I am indicating the end of proof with "QED" (Quod Erat Demonstrandum).
**)

Example Exercise_1
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P)
        (Pr_2: P -> Q)
        (Pr_3: Q -> R)
        (Pr_4: R -> S) : S.
Proof.
        assert (MPP_6 := Pr_2 (Pr_1) : Q).
        assert (MPP_7 := Pr_3 (MPP_6) : R).
        assert (MPP_8 := Pr_4 (MPP_7) : S).
        exact MPP_8.
Qed.



(** Example Exercise_2 is equivalent to this
*** symbolic proof which is mostly in Hardegree's notation.
***
*** (1) P → Q       Pr
*** (2) Q → R       Pr
*** (3) R → S       Pr
*** (4) ~ S         Pr
*** (5) SHOW: ~ P   DD
*** (6) |   ~ R     3,4,MTT
*** (7) |   ~ Q     2,6,MTT
*** (8) |   ~ P     1,7,MTT,QED
***
*** Note: "MPP" indicates Modus Tollendo Tollens
*** (Hardegree would use →O instead.)
**)

Example Exercise_2
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P -> Q)
        (Pr_2: Q -> R)
        (Pr_3: R -> S)
        (Pr_4: not S) : not P.
Proof.
        (* "unfold" changes Pr_4 to "Pr_4 : S -> False". *)
        unfold not in Pr_4.

        assert (Modus_tollendo_tollens_6 : not R).
        {
            (* "unfold" changes Pr_4 to "Pr_4 : S -> False". *)
            unfold not.
            intro Rx.
            assert (Sx := Pr_3 (Rx) : S).
            assert (false_x := Pr_4 (Sx) : False).
            exact false_x.
        }

        assert (Modus_tollendo_tollens_7 : not Q).
        {
            unfold not.
            intro Qx.
            assert (Rx := Pr_2 (Qx) : R).
            assert (false_x := Modus_tollendo_tollens_6 (Rx) : False).
            exact false_x.
        }

        assert (Modus_tollendo_tollens_8 : not P).
        {
            unfold not.
            intro Px.
            assert (Qx := Pr_1 (Px) : Q).
            assert (false_x := Modus_tollendo_tollens_7 (Qx) : False).
            exact false_x.
        }

        exact Modus_tollendo_tollens_8.
Qed.


(** Example Exercise_2_second_version is equivalent to
*** example Exercise_2, but is much simpler.
***
*** Because "not R" is defined as "R -> False",
*** and because Pr_4 has the type "not S" (which means "S -> False"),
*** and because Pr_3 has the type "R -> S",
*** we only need to define a function that,
*** from a parameter (Rx : R), computes Pr_5 (Pr_4 (Rx)).
**)

Example Exercise_2_second_version
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P -> Q)
        (Pr_2: Q -> R)
        (Pr_3: R -> S)
        (Pr_4: not S) : not P.
Proof.
        unfold not in Pr_4.

        assert (Mtt_6 := (fun (Rx : R) => Pr_4 (Pr_3 (Rx))) : not R).

        assert (Mtt_7 := (fun (Qx : Q) => Mtt_6 (Pr_2 (Qx))) : not Q).

        assert (Mtt_8 := (fun (Px : P) => Mtt_7 (Pr_1 (Px))) : not P).

        exact Mtt_8.
Qed.


End Hardegree_5_22.

(** To simplify further proofs using Modus Tollendo Tollens,
*** we can define a function that returns a "not S"
*** given an "S implies D" and a "not D" (in that order). **)

Section Modus_tollendo_tollens.

Definition Modus_toll_toll {S : Prop} {D : Prop}
        (S_implies_D : S -> D)
        (not_D : not D)
        : not S
        := fun (Sx : S) => not_D (S_implies_D (Sx)).

End Modus_tollendo_tollens.

Section Hardegree_5_22.

Example Exercise_2_third_version
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P -> Q)
        (Pr_2: Q -> R)
        (Pr_3: R -> S)
        (Pr_4: not S) : not P.
Proof.
        assert (MTT_6 := Modus_toll_toll (Pr_3) (Pr_4) : not R).

        assert (MTT_7 := Modus_toll_toll (Pr_2) (MTT_6) : not Q).

        assert (MTT_8 := Modus_toll_toll (Pr_1) (MTT_7) : not P).

        exact MTT_8.
Qed.



Example Exercise_3_first_version
  (P:Prop) (Q:Prop) (R:Prop)
  (Pr_1: or (not (P)) (Q))
  (Pr_2: not (Q))
  (Pr_3: or (P) (R)) : R.
Proof.
  assert (MTPs_5 : not P).
  {
    destruct Pr_1 as [ not_Px | Qx ].
    { exact not_Px. }
    { assert (false_x := Pr_2 (Qx) : False). contradiction false_x. }
  }

  assert (MTPd_6 : R).
  {
    destruct Pr_3 as [ Py | Ry ].
    { assert (false_y := MTPs_5 (Py) : False). contradiction false_y. }
    { exact Ry. }
  }

  exact MTPd_6.
Qed.

Example Exercise_3_second_version
  (P : Prop) (Q : Prop) (R : Prop)
  (Pr_1: or (not (P)) (Q))
  (Pr_2: not (Q))
  (Pr_3: or (P) (R)) : R.
Proof.
  assert (MTPs_5 :=
    (match Pr_1 return (not P)
    with or_introl (_ as not_Px) =>
      not_Px
    | or_intror (_ as Qx) =>
      match Pr_2 (Qx) return (not P) with end
    end) : not P).

  assert (MTPd_6 :=
    (match Pr_3 return R
    with or_introl (_ as Px) =>
        match MTPs_5 (Px) return R with end
    | or_intror (_ as Rx) =>
        Rx
    end) : R).

  exact MTPd_6.
Qed.

End Hardegree_5_22.

Section Modus_tollendo_ponens_sinistrum.

Definition Modus_toll_pon_sinis {S : Prop} {D : Prop}
        (Sx_or_Dx : or S D)
        (not_Dx   : not D) : S
        := match Sx_or_Dx return S
        with or_introl (_ as Sx) =>
                Sx
        | or_intror Dx =>
                (match not_Dx (Dx) return S with end)
        end.

End Modus_tollendo_ponens_sinistrum.

Section Modus_tollendo_ponens_dextrum.

Definition Modus_toll_pon_dex {S : Prop} {D : Prop}
        (Sx_or_Dx : or S D)
        (not_Sx   : not S) : D
        := match Sx_or_Dx return D
        with or_introl (_ as Sx) =>
                (match not_Sx (Sx) return D with end)
        | or_intror (_ as Dx) =>
                Dx
        end.

End Modus_tollendo_ponens_dextrum.


Section Hardegree_5_22.

Example Exercise_3_again
  (P:Prop) (Q:Prop) (R:Prop)
  (Pr_1: or (not(P)) (Q))
  (Pr_2: not (Q))
  (Pr_3: or (P) (R)) : R.
Proof.
  assert (MTPs_5 := Modus_toll_pon_sinis (Pr_1) (Pr_2) : not P).
  assert (MTPd_6 := Modus_toll_pon_dex (Pr_3) (MTPs_5) : R).
  exact MTPd_6.
Qed.

Example Exercise_4
	(P : Prop) (Q : Prop) (R : Prop)
	(Pr1: or P Q)
	(Pr2: not P)
	(Pr3: Q -> R) : R.
Proof.
	assert (MTPd4 := Modus_toll_pon_dex (Pr1)(Pr2) : Q).
	assert (MPP5 := Pr3 (MTPd4) : R).
	exact MPP5.
Qed.

Example Exercise_5 
	(P Q R S : Prop)
 	(Pr_1: P)
 	(Pr_2: P -> (not Q))
 	(Pr_3: R -> Q)
 	(Pr_4: (not R) -> S) : S.
Proof.
	pose (Mpp_5 := Pr_2 Pr_1 : not Q).
	pose (Mtt_6 := Modus_toll_toll (Pr_3) (Mpp_5) : not R).
	pose (Mpp_7 := Pr_4 (Mtt_6) : S).
	exact Mpp_7.
Qed.


Example Exercise_6
	(P Q R S : Prop)
	(Pr_1: or (P) (not Q))
	(Pr_2: not P)
	(Pr_3: R -> Q)
	(Pr_4: (not R) -> S) : S.
Proof.
	pose (MTPd_5 := Modus_toll_pon_dex (Pr_1) (Pr_2) : not Q).
	pose (Mtt_6 := Modus_toll_toll (Pr_3) (MTPd_5) : not R).
	pose (Mpp_7 := Pr_4 (Mtt_6) : S).
	exact Mpp_7.
Qed.


Example Exercise_7
	(P Q : Prop)
	(Pr_1 : (P -> Q) -> P)
	(Pr_2 : P -> Q) : Q.        
Proof.
	pose (Mpp_3 := Pr_1 (Pr_2) : P).
	pose (Mpp_4 := Pr_2 (Mpp_3) : Q).
	exact Mpp_4.
Qed.


Example Exercise_8
	(P Q R : Prop)
	(Pr_1 : (P -> Q) -> R)
	(Pr_2 : R -> P)
	(Pr_3 : P -> Q) : Q.
Proof.
	pose (Mpp_4 := Pr_1 (Pr_3) : R).
	pose (Mpp_5 := Pr_2 (Mpp_4) : P).
	pose (Mpp_6 := Pr_3 (Mpp_5) : Q).
	exact Mpp_6.
Qed.


Example Exercise_9
	(P Q R : Prop)
	(Pr_1 : (P -> Q) -> (Q -> R))
	(Pr_2 : P -> Q)
	(Pr_3 : P) : R.
Proof.
	pose (Mpp_5 := Pr_1 (Pr_2) : Q -> R).
	pose (Mpp_6 := Pr_2 (Pr_3) : Q).
	pose (Mpp_7 := Mpp_5 (Mpp_6) : R).
	exact Mpp_7.
Qed.


Example Exercise_10
	(P Q R : Prop)
	(Pr_1 : (not P) -> Q)
	(Pr_2 : not Q)
	(Pr_3 : or (R) (not P)) : R.
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_1) (Pr_2) : not (not P)).
	pose (MTPs_5 := Modus_toll_pon_sinis (Pr_3) (Mtt_4) : R).
	exact MTPs_5.
Qed.


Example Exercise_11
	(P Q R : Prop)
	(Pr_1 : (not P) -> (or (not Q) (R)))
	(Pr_2 : P -> R)
	(Pr_3 : not R) : not Q.
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_2) (Pr_3) : not P).
	pose (Mpp_5 := Pr_1 (Mtt_4) : or (not Q) (R)).
	pose (MTPs_6 := Modus_toll_pon_sinis (Mpp_5) (Pr_3) : not Q).
	exact MTPs_6.
Qed.


Example Exercise_12
	(P Q S : Prop)
	(Pr_1 : P -> (not Q))
	(Pr_2 : (not S) -> P)
	(Pr_3 : not (not Q)) : not (not S).
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_1) (Pr_3) : not P).
	pose (Mtt_5 := Modus_toll_toll (Pr_2) (Mtt_4): not (not S)).
	exact Mtt_5.
Qed.


Example Exercise_13
	(P Q R : Prop)
	(Pr_1 : or P Q)
	(Pr_2 : Q -> R)
	(Pr_3 : not R) : P.
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_2) (Pr_3) : not Q).
	pose (MTPs_5 := Modus_toll_pon_sinis (Pr_1) (Mtt_4) : P).
	exact MTPs_5.
Qed.


Example Exercise_14
	(P Q R : Prop)
	(Pr_1 : (not P) -> (or Q R))
	(Pr_2 : P -> Q)
	(Pr_3 : not Q) : R.
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_2) (Pr_3) : not P).
	pose (Mpp_5 := Pr_1 (Mtt_4) : or Q R).
	pose (MTPd_6 := Modus_toll_pon_dex (Mpp_5) (Pr_3) : R).
	exact MTPd_6.
Qed.


Example Exercise_15
	(P R S : Prop)
	(Pr_1 : P -> R)
	(Pr_2 : (not P) -> (or S R))
	(Pr_3 : not R) : S.
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_1) (Pr_3) : not P).
	pose (Mpp_5 := Pr_2 (Mtt_4) : or S R).
	pose (MTPs_6 := Modus_toll_pon_sinis (Mpp_5) (Pr_3) : S).
	exact MTPs_6.
Qed.


Example Exercise_16
	(P Q R S : Prop)
	(Pr_1 : or (P) (not Q))
	(Pr_2 : (not R) -> not (not Q))
	(Pr_3 : R -> not S)
	(Pr_4 : not (not S)) : P.
Proof.
	pose (Mtt_5 := Modus_toll_toll (Pr_3) (Pr_4) : not R).
	pose (Mpp_6 := Pr_2 (Mtt_5) : not (not Q)).
	pose (MTPs_7 := Modus_toll_pon_sinis (Pr_1) (Mpp_6) : P).
	exact MTPs_7.
Qed.


Example Exercise_17
	(P Q R S : Prop)
	(Pr_1 : or (P -> Q) (R -> S))
	(Pr_2 : (P -> Q) -> R)
	(Pr_3 : not R) : R -> S.
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_2) (Pr_3) : not (P -> Q)).
	pose (MTPd_5 := Modus_toll_pon_dex (Pr_1) (Mtt_4) : R -> S).
	exact MTPd_5.
Qed.


Example Exercise_18
	(P Q R S : Prop) (T : Prop)
	(Pr_1 : (P -> Q) -> (R -> S))
	(Pr_2 : or (R -> T) (P -> Q))
	(Pr_3 : not (R -> T)) : R -> S.
Proof.
	pose (MTPd_4 := Modus_toll_pon_dex (Pr_2) (Pr_3) : P -> Q).
	pose (Mpp_5 := Pr_1 (MTPd_4) : R -> S).
	exact Mpp_5.
Qed.


Example Exercise_19
	(P Q R : Prop)
	(Pr_1 : (not R) -> or (P) (Q))
	(Pr_2 : R -> P)
	(Pr_3 : (R -> P) -> (not P)) : Q.
Proof.
	pose (Mpp_4 := Pr_3 (Pr_2) : not P).
	pose (Mtt_5 := Modus_toll_toll (Pr_2) (Mpp_4) : not R).
	pose (Mpp_6 := Pr_1 (Mtt_5) : or (P) (Q)).
	pose (MTPd_7 := Modus_toll_pon_dex (Mpp_6) (Mpp_4) : Q).
	exact MTPd_7.
Qed.


Example Exercise_20
	(P Q R : Prop)
	(Pr_1 : or (P -> Q) (R))
	(Pr_2 : (or (P -> Q) (R)) -> not R)
	(Pr_3 : (P -> Q) -> (Q -> R)) : not Q.
Proof.
	pose (Mpp_4 := Pr_2 (Pr_1) : not R).
	pose (MTPd_5 := Modus_toll_pon_sinis (Pr_1) (Mpp_4) : P -> Q).
	pose (Mpp_6 := Pr_3 (MTPd_5) : Q -> R).
	pose (Mtt_7 := Modus_toll_toll (Mpp_6) (Mpp_4) : not Q).
	exact Mtt_7.
Qed.


Example Exercise_21
	(P Q R S : Prop)
	(Pr_1 : and P Q)
	(Pr_2 : P -> (and R S))
	: and Q S.
Proof.
	pose (Simplification_3 := proj1 Pr_1 : P).
	pose (Simplification_4 := proj2 Pr_1 : Q).
	pose (Mpp_5 := Pr_2 (Simplification_3) : and R S).
	pose (Simplification_6 := proj2 (Mpp_5) : S).
	pose (Adjunction_7
		:= conj (Simplification_4) (Simplification_6)
		: and Q S).
	exact Adjunction_7.
Qed.


Example Exercise_22 (P Q R S : Prop)
	(Pr_1 : and P Q)
	(Pr_2 : (or P R) -> S)
	: and P S.
Proof.
	pose (Simp_3 := proj1 (Pr_1) : P).
	pose (Addition_4 := or_introl (Simp_3) : or P R).   
	pose (Mpp_5 := Pr_2 (Addition_4) : S).
	pose (Adj_6 := conj (Simp_3) (Mpp_5) : and P S).
	exact Adj_6.
Qed.


Example Exercise_23
	(P Q R S : Prop) (T : Prop) (U : Prop)
	(Pr_1 : P)
	(Pr_2 : (or P Q) -> (and R S))
	(Pr_3 : (or R T) -> U)
	: U.
Proof.
	pose (Add_4 := or_introl (Pr_1) : or P Q).
	pose (Mpp_5 := Pr_2 (Add_4) : and R S).
	pose (Simp_6 := proj1 (Mpp_5) : R).
	pose (Add_7 := or_introl (Simp_6) : or R T).
	pose (Mpp_8 := Pr_3 (Add_7) : U).
	exact Mpp_8.
Qed.


Example Exercise_24
	(P Q R : Prop)
	(Pr_1 : P -> Q)
	(Pr_2 : or P R)
	(Pr_3 : not Q)
	: and R (not P).
Proof.
	pose (Mtt_4 := Modus_toll_toll (Pr_1) (Pr_3) : not P).
	pose (MTPd_5 := Modus_toll_pon_dex (Pr_2) (Mtt_4) : R).
	pose (Adj_6 := conj (MTPd_5) (Mtt_4) : and R (not P)).
	exact Adj_6.
Qed.


Example Exercise_25
	(P Q R S : Prop) (T : Prop)
	(Pr_1 : P -> Q)
	(Pr_2 : (not R) -> (Q -> S))
	(Pr_3 : R -> T)
	(Pr_4 : and (not T) (P))
	: and Q S.
Proof.
	pose (Simp_5 := proj1 (Pr_4) : not T).
	pose (Simp_6 := proj2 (Pr_4) : P).
	pose (Mtt_7 := Modus_toll_toll (Pr_3) (Simp_5) : not R).
	pose (Mpp_8 := Pr_2 (Mtt_7) : Q -> S).
	pose (Mpp_9 := Pr_1 (Simp_6) : Q).
	pose (Mpp_10 := Mpp_8 (Mpp_9) : S).
	pose (Adj_11 := conj (Mpp_9) (Mpp_10) : and Q S).
	exact Adj_11.
Qed.


Example Exercise_26
	(P Q R S : Prop) (T : Prop)
	(Pr_1 : P -> Q)
	(Pr_2 : or (R) (not Q))
	(Pr_3 : and (not R) (S))
	(Pr_4 : (and (not P) (S)) -> T)
	: T.
Proof.
	pose (Simp_5 := proj1 (Pr_3) : not R).
	pose (MTPd_6 := Modus_toll_pon_dex (Pr_2) (Simp_5) : not Q).
	pose (Mtt_7 := Modus_toll_toll (Pr_1) (MTPd_6) : not P).
	pose (Simp_8 := proj2 (Pr_3) : S).
	pose (Adj_9 := conj (Mtt_7) (Simp_8) : (and (not P) (S))).
	pose (Mpp_10 := Pr_4 (Adj_9) : T).
	exact Mpp_10.
Qed.

End Hardegree_5_22.

Definition Double_negation
	{Premise_t : Prop} (premise : Premise_t)
	: not (not (Premise_t))
        := (let prem_impl_false_impl_false
		(prem_impl_false : Premise_t -> False) : False
                := prem_impl_false (premise)
                in prem_impl_false_impl_false).

Section Hardegree_5_22.

Example Exercise_27
	(P Q R S : Prop)
	(Pr_1 : or (P) (not Q))
	(Pr_2 : (not R) -> Q)
	(Pr_3 : R -> (not S))
	(Pr_4 : S)
	: P.
Proof.
	pose (Dn_5 := Double_negation (Pr_4) : not (not S)).
	pose (Mtt_6 := Modus_toll_toll (Pr_3) (Dn_5) : not R).
	pose (Mpp_7 := Pr_2 (Mtt_6) : Q).
	pose (Dn_8 := Double_negation (Mpp_7) : not (not Q)).
	pose (MTPs_9 := Modus_toll_pon_sinis (Pr_1) (Dn_8) : P).
	exact MTPs_9.
Qed.


Example Exercise_28 (P Q R S : Prop) (T : Prop)
        (Pr_1 : and P Q)
        (Pr_2 : (or P T) -> R)
        (Pr_3 : S -> not R)
        : not S.
Proof.
        pose (Simp_4 := proj1 (Pr_1) : P).
        pose (Add5 := or_introl (Simp_4) : or P T).
        pose (Mpp_6 := Pr_2 (Add5) : R).
        pose (Dn_7 := Double_negation (Mpp_6) : not (not R)).
        pose (Mtt_8 := Modus_toll_toll (Pr_3) (Dn_7) : not S).
        exact Mtt_8.
Qed.


Example Exercise_29 (P Q R S : Prop)
        (Pr_1 : and P Q)
        (Pr_2 : P -> R)
        (Pr_3 : (and P R) -> S)
        : (and Q S).
Proof.
        pose (Simp_4 := proj1 (Pr_1) : P).
        pose (Simp_5 := proj2 (Pr_1) : Q).
        pose (Mpp_6 := Pr_2 (Simp_4) : R).
        pose (Adj_7 := conj (Simp_4) (Mpp_6) : and P R).
        pose (Mpp_8 := Pr_3 (Adj_7) : S).
        pose (Adj_9 := conj (Simp_5) (Mpp_8) : and Q S).
        exact Adj_9.
Qed.

Example Exercise_30 (P Q R S : Prop)
        (Pr_1 : P -> Q)
        (Pr_2 : or Q R)
        (Pr_3 : (and R (not P)) -> S)
        (Pr_4 : not Q)
        : S.
Proof.
        pose (Mtt_5 := Modus_toll_toll (Pr_1) (Pr_4) : not P).
        pose (MTPd_6 := Modus_toll_pon_dex (Pr_2) (Pr_4) : R).
        pose (Adj_7 := conj (MTPd_6) (Mtt_5) : and R (not P)).
        pose (Mpp_8 := Pr_3 (Adj_7) : S).
        exact Mpp_8.
Qed.


Example Exercise_31 (P Q : Prop)
	(Pr_1 : and P Q)
	: and Q P.
Proof.
	pose (Simp_2 := proj1 (Pr_1) : P).
	pose (Simp_3 := proj2 (Pr_1) : Q).
	pose (Adj_4 := conj (Simp_3) (Simp_2) : and Q P).
	exact Adj_4.
Qed.


Example Exercise_32 (P Q R : Prop)
	(Pr_1 : and P (and Q R))
	: and (and P Q) R.
Proof.
	pose (Simp_2 := proj1 (Pr_1) : P).
	pose (Simp_3 := proj2 (Pr_1) : and Q R).
	pose (Simp_4 := proj1 (Simp_3) : Q).
	pose (Simp_5 := proj2 (Simp_3) : R).
	pose (Adj_6 := conj (Simp_2) (Simp_4) : and P Q).
	pose (Adj_7 := conj (Adj_6) (Simp_5) : and (and P Q) R).
	exact Adj_7.
Qed.


Example Exercise_33 (P : Prop)
	(Pr_1 : P) : and (P) (P).
Proof.
	pose (Adj_2 := conj (Pr_1) (Pr_1) : and (P) (P)).
	exact Adj_2.
Qed.


Example Exercise_34 (P Q : Prop)
	(Pr_1 : P) : and (P) (or (P) (Q)).
Proof.
	pose (Add_2 := or_introl (Pr_1) : or (P) (Q)).
	pose (Adj_3 := conj (Pr_1) (Add_2) : and (P) (or (P) (Q))).
	exact Adj_3.
Qed.


Example Exercise_35_Hardegree (P Q : Prop)
	(Pr_1 : and (P) (not P)) : Q.
Proof.
	pose (Simp_2 := proj1 (Pr_1) : P).
	pose (Simp_3 := proj2 (Pr_1) : not P).
	pose (Contradiction_In_4 := Simp_3 (Simp_2) : False).

	pose (Contradiction_Out_5 :=
		match Contradiction_In_4 return Q with end).

	exact Contradiction_Out_5.
Qed.


Example Exercise_36 (P Q S : Prop)
  (Pr_1 : iff (P) (not Q))
	(Pr_2 : Q)
	(Pr_3 : iff (P) (not S))
  (Dn_S : not (not S) -> S)
	: S.
Proof.
	assert (Simp_4 := proj1 (Pr_1) : P -> not Q).

	assert (Dn_5 := Double_negation Pr_2 : not (not Q)).

	assert (Mtt_6 := Modus_toll_toll (Simp_4) (Dn_5) : not P).

	assert (Simp_7 := proj2 (Pr_3) : (not S) -> P).
        
	assert (Mtt_8 := Modus_toll_toll (Simp_7) (Mtt_6)
		: not (not S)).

	assert (Dn_9 := Dn_S (Mtt_8) : S).

	exact Dn_9.
Qed.


(*
Example Exercise_37 (P Q R S T : Prop)
	(Pr_1 : and P (not (Q)))
	(Pr_2 : or (Q) (P -> S))
	(Pr_3 : iff (and R T) (S))
	: and P R.
Proof.
	assert (Simp_4 := proj1 (Pr_1)).
	assert (Simp_5 := proj2 (Pr_1)).
	assert (MTPd_6 := Modus_tollendo_ponens_right (Pr_2) (Simp_5)).
	assert (Mpp_7 := MTPd_6 (Simp_4)).
	assert (Bicond_8 := proj2 (Pr_3)).
	assert (Mpp_9 := Bicond_8 (Mpp_7)).
	assert (Simp_10 := proj1 Mpp_9).
	assert (Conj_11 := conj Simp_4 Simp_10).
	exact Conj_11.
Quit.
*)

End Hardegree_5_22.
