Require Import Specification DemonicComposition Statement Predicative.

Require Import Lia.

Open Scope stmt_scope.

Definition spec : Stmt (nat * nat) := ⟨fun '(x,y) '(x',y') => x >= y /\ x' = y /\ y' = x⟩.

Definition prog : Stmt (nat*nat) := $(x,y) := (x - y, y); $(x,y) := (x, x + y); $(x,y) := (y - x, y).

Theorem correctness : prog ⊑ spec.
Proof.
  unfold refines.
  intros (x,y) ((u,v),(HHxy,_)).
  split.
  { intros (x',y').
    intros (((a,b), (HH11,(((c,d),(HH,HH')),HH122))),HH2).
    simpl in HH11,HH,HH'.
    simpl in *.
    inversion HH11; subst a b; clear HH11.
    inversion HH; subst c d; clear HH.
    inversion HH'; subst x' y'; clear HH'.
    repeat split; try lia.
  }
  { exists (y,x).
    split.
    { exists (x - y,y); split.
      { reflexivity. }
      { split.
        { exists (x - y, x - y + y); split.
          { reflexivity. }
          { simpl; f_equal; lia. }
        }
        { intros (a,b) HHpred; simpl in HHpred.
          inversion_clear HHpred.
          exists (x - y + y - (x - y), x - y + y); reflexivity.
        }
      }
    }
    { intros (a,b) HHpred.
      inversion HHpred; subst a b; clear HHpred.
      exists ((x-y) + y - (x - y), (x - y) + y).
      split.
      { exists (x - y, x - y + y); split; reflexivity. }
      { intros (a,b) HHab.
        inversion HHab; subst a b; clear HHab.
        exists ((x - y + y) - (x - y), x - y + y); reflexivity.
      }
    }
  }
Qed.

Print Assumptions correctness.
    
Close Scope stmt_scope.