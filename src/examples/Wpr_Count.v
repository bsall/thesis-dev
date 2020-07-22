Require Import ZArith.

Require Import Statement ImprovedPredicative Wpr.

Require Import Lia.

Open Scope stmt_scope.

Definition spec := ⟨fun '(i,n) '(i',n') => i <= n /\ i' = n /\ n = n'⟩.

Definition prog := WWhile (fun '(i,n) => i <> n) Do $(i,n) := (i+1,n) Done.


Theorem correctness : prog ⊑ spec.
Proof.
  intros (i,n) ((u,v),(HHin,_)); clear u v.
  set (K := wpr prog (pred spec)).
  generalize i HHin; clear i HHin.
  induction n; intros i HHin.
  { apply wpr_while_construct; right; simpl. lia. }
  { apply Lt.le_lt_or_eq in HHin.
    destruct HHin as [ HHin | HHin ].
    { assert (i <= n) as HHin' by lia. 
      cut ((fun '(i,n) '(i',n') => i' <= n' /\ K (i,S n) (i',S n')) (i, n) (i, n)).
      { intros (HH1,HH2); auto. }
      { apply (IHn _ HHin'); clear i n HHin HHin' IHn.
        intros (i,n) (i',n'). intros [ (HHin,(HHi'n',HHind)) | HH ]; split; try lia.
        { apply wpr_while_construct; left; split; auto. lia. }
        { simpl in HH; apply wpr_while_construct; left; split; try lia; fold prog K.
          apply wpr_while_construct; right; simpl. lia.
        }
      }
    }
    { apply wpr_while_construct; right; simpl. lia. }
  }
Qed.


