Module Four.

Inductive Day_of_the_Week : Set :=
Monday | Tuesday | Wednesday
| Thursday | Friday
| Saturday | Sunday.

Inductive Month_of_the_Year : Set :=
January | February | March
| April | May | June
| July | August | September
| October | November | December.

Theorem Day_must_be_MTWTFSS :
forall d : Day_of_the_Week,
or (eq d Monday) (or (eq d Tuesday)
(or (eq d Wednesday) (or (eq d Thursday)
(or (eq d Friday) (or (eq d Saturday)
(eq d Sunday)))))).

Proof.

intro d.

destruct d.

assert (A1 := eq_refl : eq Monday Monday).

assert (A2 := or_introl A1 : or
 (eq Monday Monday)
 (or (eq Monday Tuesday)
 (or (eq Monday Wednesday)
 (or (eq Monday Thursday)
 (or (eq Monday Friday)
 (or (eq Monday Saturday)
 (eq Monday Sunday))))))).

exact A2.

assert (B1 := eq_refl : eq Tuesday Tuesday).

assert (B2 := or_introl B1 : or
  (eq Tuesday Tuesday)
  (or (eq Tuesday Wednesday)
  (or (eq Tuesday Thursday)
  (or (eq Tuesday Friday)
  (or (eq Tuesday Saturday)
  (eq Tuesday Sunday)))))).

assert (B3 := or_intror B2 : or
  (eq Tuesday Monday)
  (or (eq Tuesday Tuesday)
  (or (eq Tuesday Wednesday)
  (or (eq Tuesday Thursday)
  (or (eq Tuesday Friday)
  (or (eq Tuesday Saturday)
  (eq Tuesday Sunday))))))).

exact B3.

assert (C1 := eq_refl : eq Wednesday Wednesday).

assert (C2 := or_introl C1 :
  or (eq Wednesday Wednesday)
  (or (eq Wednesday Thursday)
  (or (eq Wednesday Friday)
  (or (eq Wednesday Saturday)
  (eq Wednesday Sunday))))).

assert (C3 := or_intror C2 :
  or (eq Wednesday Tuesday)
  (or (eq Wednesday Wednesday)
  (or (eq Wednesday Thursday)
  (or (eq Wednesday Friday)
  (or (eq Wednesday Saturday)
  (eq Wednesday Sunday)))))).

assert (C4 := or_intror C3 :
  or (eq Wednesday Monday)
  (or (eq Wednesday Tuesday)
  (or (eq Wednesday Wednesday)
  (or (eq Wednesday Thursday)
  (or (eq Wednesday Friday)
  (or (eq Wednesday Saturday)
  (eq Wednesday Sunday))))))).

exact C4.

assert (D1 := eq_refl : eq Thursday Thursday).

assert (D2 := or_introl D1 :
  or (eq Thursday Thursday)
  (or (eq Thursday Friday)
  (or (eq Thursday Saturday)
  (eq Thursday Sunday)))).

assert (D3 := or_intror D2 :
  or (eq Thursday Wednesday)
  (or (eq Thursday Thursday)
  (or (eq Thursday Friday)
  (or (eq Thursday Saturday)
  (eq Thursday Sunday))))).

assert (D4 := or_intror D3 :
  or (eq Thursday Tuesday)
  (or (eq Thursday Wednesday)
  (or (eq Thursday Thursday)
  (or (eq Thursday Friday)
  (or (eq Thursday Saturday)
  (eq Thursday Sunday)))))).

assert (D5 := or_intror D4 :
  or (eq Thursday Monday)
  (or (eq Thursday Tuesday)
  (or (eq Thursday Wednesday)
  (or (eq Thursday Thursday)
  (or (eq Thursday Friday)
  (or (eq Thursday Saturday)
  (eq Thursday Sunday))))))).

exact D5.

assert (E1 := eq_refl : eq Friday Friday).

assert (E2 := or_introl E1 :
  or (eq Friday Friday)
  (or (eq Friday Saturday)
  (eq Friday Sunday))).

assert (E3 := or_intror E2 :
  or (eq Friday Thursday)
  (or (eq Friday Friday)
  (or (eq Friday Saturday)
  (eq Friday Sunday)))).

assert (E4 := or_intror E3 :
  or (eq Friday Wednesday)
  (or (eq Friday Thursday)
  (or (eq Friday Friday)
  (or (eq Friday Saturday)
  (eq Friday Sunday))))).

assert (E5 := or_intror E4 :
  or (eq Friday Tuesday)
  (or (eq Friday Wednesday)
  (or (eq Friday Thursday)
  (or (eq Friday Friday)
  (or (eq Friday Saturday)
  (eq Friday Sunday)))))).

assert (E6 := or_intror E5 :
  or (eq Friday Monday)
  (or (eq Friday Tuesday)
  (or (eq Friday Wednesday)
  (or (eq Friday Thursday)
  (or (eq Friday Friday)
  (or (eq Friday Saturday)
  (eq Friday Sunday))))))).

exact E6.

assert (F1 := eq_refl : eq Saturday Saturday).

assert (F2 := or_introl F1 :
  or (eq Saturday Saturday)
  (eq Saturday Sunday)).

assert (F3 := or_intror F2 :
  or (eq Saturday Friday)
  (or (eq Saturday Saturday)
  (eq Saturday Sunday))).

assert (F4 := or_intror F3 :
  or (eq Saturday Thursday)
  (or (eq Saturday Friday)
  (or (eq Saturday Saturday)
  (eq Saturday Sunday)))).

assert (F5 := or_intror F4 :
  or (eq Saturday Wednesday)
  (or (eq Saturday Thursday)
  (or (eq Saturday Friday)
  (or (eq Saturday Saturday)
  (eq Saturday Sunday))))).

assert (F6 := or_intror F5 :
  or (eq Saturday Tuesday)
  (or (eq Saturday Wednesday)
  (or (eq Saturday Thursday)
  (or (eq Saturday Friday)
  (or (eq Saturday Saturday)
  (eq Saturday Sunday)))))).

assert (F7 := or_intror F6 :
  or (eq Saturday Monday)
  (or (eq Saturday Tuesday)
  (or (eq Saturday Wednesday)
  (or (eq Saturday Thursday)
  (or (eq Saturday Friday)
  (or (eq Saturday Saturday)
  (eq Saturday Sunday))))))).

exact F7.

assert (G1 := eq_refl : eq Sunday Sunday).

assert (G2 := or_intror G1 :
  or (eq Sunday Saturday)
  (eq Sunday Sunday)).

assert (G3 := or_intror G2 :
  or (eq Sunday Friday)
  (or (eq Sunday Saturday)
  (eq Sunday Sunday))).

assert (G4 := or_intror G3 :
  or (eq Sunday Thursday)
  (or (eq Sunday Friday)
  (or (eq Sunday Saturday)
  (eq Sunday Sunday)))).

assert (G5 := or_intror G4 :
  or (eq Sunday Wednesday)
  (or (eq Sunday Thursday)
  (or (eq Sunday Friday)
  (or (eq Sunday Saturday)
  (eq Sunday Sunday))))).

assert (G6 := or_intror G5 :
  or (eq Sunday Tuesday)
  (or (eq Sunday Wednesday)
  (or (eq Sunday Thursday)
  (or (eq Sunday Friday)
  (or (eq Sunday Saturday)
  (eq Sunday Sunday)))))).

assert (G7 := or_intror G6 :
  or (eq Sunday Monday)
  (or (eq Sunday Tuesday)
  (or (eq Sunday Wednesday)
  (or (eq Sunday Thursday)
  (or (eq Sunday Friday)
  (or (eq Sunday Saturday)
  (eq Sunday Sunday))))))).

exact G7.

Qed.

End Four.