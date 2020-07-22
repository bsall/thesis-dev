Require Import Statement ImprovedPredicative.

Require Import ZArith Lia.

Open Scope Z_scope.

Open Scope stmt_scope.

Definition spec : Stmt (Z*Z) := ⟨fun '(x,y) '(x',y') => x' = y /\ y' = x⟩.

Definition prog := $(x,y) := (x - y, y); $(x,y) := (x, x + y); $(x,y) := (y - x, y).

Theorem correctness : prog ⊑ spec.
Proof.
  intros (x,y) ((u,v),_); clear u v.
  split.
  { intros (x',y'); simpl.
    intros HHeq; inversion_clear HHeq.
    lia.
  }
  { exists (y,x); simpl. f_equal; lia. }
Qed.

Print Assumptions correctness.

Definition prog' := $(x,y) := (x + y, y); $(x,y) := (x, x - y); $(x,y) := (x - y, y).

Theorem equiv : forall s s', pred prog s s' <-> pred prog' s s'.
Proof.
  intros (x,y) (x',y'); simpl.
  split; intros H; inversion H; subst; f_equal.
  all : lia.
Qed.

Print Assumptions equiv.

Close Scope stmt_scope.