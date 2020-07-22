Require Import CbC.

Open Scope cbc_scope.

Unset Program Cases.

Program Definition Swap :=
  ⟨ fun '(x,y) '(x',y')  => x' = y /\ y' = x ⟩ :{
    '(x,y) := (y,x) :{
       '(x,y) := (x+y, y);
       '(x,y) := (x, x-y);
       '(x,y) := (x-y, y)
     }                
   }.

Require Import Lia.

Next Obligation. intros; destruct s; simpl; f_equal; lia. Qed. 

Next Obligation. intros; destruct s; simpl; auto. Qed. 
                 
Theorem proof : (Π2 Swap) ⊑ (Π1 Swap).
Proof. apply (CbC.soundness Swap). Qed.

Print Assumptions proof.

Close Scope cbc_scope.
