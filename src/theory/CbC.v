Require Import Predicate Specification Statement Predicative.

Open Scope stmt_scope.

Reserved Notation "'φ' d" (at level 70, no associativity).
Reserved Notation "'π1' d" (at level 70, no associativity).
Reserved Notation "'π2' d" (at level 70, no associativity).

Inductive Dev { T } : Type -> bool -> Type :=
| Void : forall { V }, @Dev T V true
| Spec : forall { V }, @Specification T V -> @Dev T V true
| Assignment : forall { V }, (T -> V) -> @Dev T V true
| Seq : forall { U V b1 b2 }, @Dev T U b1 -> @Dev U V b2 -> @Dev T V (andb b1 b2)
| If : forall { V b1 b2 } (p : T -> Prop), @Dev T V b1 -> @Dev T V b2 -> @Dev T V (andb b1 b2)
| While { b } (p : T -> Prop) (d : @Dev T T b) : @Dev T T b
| Block : forall { V b }, @Dev T V true -> @Dev T V b -> @Dev T V false
| Guarded : forall { V b } (p : T -> Prop), @Dev T V b -> @Dev T V b
| Choice : forall { V b1 b2 }, @Dev T V b1 -> @Dev T V b2 -> @Dev T V (andb b1 b2).

Fixpoint dsem { T V b } (D : @Dev T V b) :=
  match D with
  | Void => (Statement.Void,Statement.Void)
  | Spec S1 => (⟨S1⟩,⟨S1⟩)
  | Assignment f => (Statement.Assignment f, Statement.Assignment f)
  | Seq d1 d2 => ((π1 d1);(π1 d2), (π2 d1);(π2 d2))
  | If p d1 d2 => (IIf p Then (π1 d1) Else (π1 d2) End, IIf p Then (π2 d1) Else (π2 d2) End)
  | While p d => (WWhile p Do (π1 d) Done, WWhile p Do (π2 d) Done)
  | Block s d => (π1 s,π2 d) 
  | Guarded p d => (WWhen p Then (π1 d) End, WWhen p Then (π2 d) End)
  | Choice d1 d2 => ((π1 d1) ⫾ (π1 d2), (π2 d1) ⫾ (π2 d2)) 
  end
where "'φ' d" := (dsem d) and "'π1' d" := (fst (dsem d)) and "'π2' d" := (snd (dsem d)).

(* Correct by Construction predicate *)

Inductive CbC : forall { T V b }, @Dev T V b -> Prop :=
| CDVoid : forall { T V }, CbC (@Void T V)
| CDSpec : forall { T V } ( S : @Specification T V ), CbC (Spec S)
| CDAssignment : forall { T V } ( f : T -> V ), CbC (Assignment f)
| CDSeq : forall {T U V b1 b2} { D1 : @Dev T U b1 } { D2 : @Dev U V b2 }, CbC D1 -> CbC D2 -> CbC (Seq D1 D2)
| CDIf : forall { T V b1 b2 } (p : T -> Prop) { D1 : @Dev T V b1 } { D2 : @Dev T V b2 },
    CbC D1 -> CbC D2 -> CbC (If p D1 D2)
| CDWhile : forall { T b } (p : T -> Prop) {D : @Dev T T b},
    CbC D
    -> well_founded (fun s s' => p s' /\ pred (π1 D) s' s /\ p s)
    -> (let K := IIf p Then π1 D End in K;K ⊑ K)
    -> CbC (While p D)
| CDBlock : forall { T V b } {S1 : @Dev T V true} {D1 : @Dev T V b},
    CbC S1 -> CbC D1 -> (π1 D1) ⊑ (π1 S1) -> CbC (Block S1 D1)
| CDGuarded : forall { T V b } (p : T -> Prop) { D : @Dev T V b }, CbC D -> CbC (Guarded p D)
| CDChoice : forall { T V b1 b2 } { D1 : @Dev T V b1 }  { D2 : @Dev T V b2 } , CbC D1 -> CbC D2 -> CbC (Choice D1 D2).

Theorem soundness : forall {T V b} {d : @Dev T V b}, CbC d -> (π2 d) ⊑ (π1 d).
Proof.
  intros T V b d HHd.
  induction HHd.
  { apply refines_reflexive. }  
  { apply refines_reflexive. }
  { apply refines_reflexive. }
  { apply (Seq_monotonic_refines _ _ _ _ _ _ _ IHHHd1 IHHHd2). }
  { apply (If_monotonic_refines _ _ _ _ _ _ _ IHHHd1 IHHHd2).  }
  { apply (refines_trans _ _ _ (WWhile p Do (π1 D) Done)).
    { apply (While_monotonic_refines _ _ _ _ IHHHd). }
    { simpl; apply refines_reflexive. }
  }
  { simpl.
    apply (refines_trans _ _ _ _ _ IHHHd2).
    exact H. 
  }
  { simpl.
    apply (When_monotonic_refines _ _ _ _ _ IHHHd).
  }
  { simpl.
    apply (Choice_monotonic_refines _ _ _ _ _ _ IHHHd1 IHHHd2).
  }
Qed.

Fixpoint s2d { T V } (S : @Stmt T V) : @Dev T V true :=
  match S with
  | Statement.Void => Void
  | Statement.Assignment f => Assignment f
  | Statement.Seq S1 S2 => Seq (s2d S1) (s2d S2)
  | Statement.If C S1 S2 => If C (s2d S1) (s2d S2)
  | Statement.While C S1 => While C (s2d S1)
  | Statement.Spec S1 => Spec S1
  | Statement.Guarded C S1 => Guarded C (s2d S1)
  | Statement.Choice S1 S2 => Choice (s2d S1) (s2d S2)
  end.

Definition Dev_ind_true : forall P : forall (T T0 : Type), Dev T0 true -> Prop,
       (forall T V : Type, P T V Void) ->
       (forall (T V : Type) (s : (T) >> (V)), P T V (Spec s)) ->
       (forall (T V : Type) (v : T -> V), P T V (Assignment v)) ->
       (forall (T U V : Type) (d : Dev U true),
        P T U d -> forall d0 : Dev V true, P U V d0 -> P T V (Seq d d0)) ->
       (forall (T V : Type) (p : T -> Prop) (d : Dev V true),
        P T V d -> forall d0 : Dev V true, P T V d0 -> P T V (If p d d0)) ->
       (forall (T : Type) (p : T -> Prop) (d : Dev T true), P T T d -> P T T (While p d)) ->
       (forall (T V : Type) (p : T -> Prop) (d : Dev V true), P T V d -> P T V (Guarded p d)) ->
       (forall (T V : Type) (d : Dev V true),
        P T V d -> forall d0 : Dev V true, P T V d0 -> P T V (Choice d d0)) ->
       forall (T T0 : Type) (d : Dev T0 true), P T T0 d.
  refine(fun (P : forall (T T0 : Type), Dev T0 true -> Prop) (f : forall T V : Type, P T V Void)
  (f0 : forall (T V : Type) (s : (T) >> (V)), P T V (Spec s)) (f1 : forall (T V : Type) (v : T -> V), P T V (Assignment v))
  (f2 : forall (T U V : Type) (d : Dev U true),
        P T U d -> forall d0 : Dev V true, P U V d0 -> P T V (Seq d d0))
  (f3 : forall (T V : Type) (p : T -> Prop) (d : Dev V true),
        P T V d -> forall d0 : Dev V true, P T V d0 -> P T V (If p d d0))
  (f4 : forall (T : Type) (p : T -> Prop) (d : Dev T true), P T T d -> P T T (While p d))
  (f6 : forall (T V : Type) (p : T -> Prop) (d : Dev V true), P T V d -> P T V (Guarded p d))
  (f7 : forall (T V : Type) (d : Dev V true),
        P T V d -> forall d0 : Dev V true, P T V d0 -> P T V (Choice d d0)) =>
fix F (T T0 : Type) (d : Dev T0 true) {struct d} : P T T0 d :=
  match d as d0 in (Dev T1 true) return (P T T1 d0) with
  | @Void _ V => f T V
  | @Spec _ V s => f0 T V s
  | @Assignment _ V v => f1 T V v
  | @Seq _ U V b1 b2 d0 d1 => _ (* f2 T U V d0 (F T U d0) d1 (F U V d1) *)
  | @If _ V b1 b2 p d0 d1 => _ (* f3 T V p d0 (F T V d0) d1 (F T V d1) *)
  | @While _ b0 p d0 => _ (* f4 T p d0 (F T T d0) *)
  | @Block _ V b0 d0 d1 => _
  | @Guarded _ V b0 p d0 => _ (* f6 T V p d0 (F T V d0) *)
  | @Choice _ V b1 b2 d0 d1 => _ (* f7 T V b1 b2 d0 (F T V b1 d0) d1 (F T V b2 d1) *)
  end).
  destruct b1,b2; simpl in *.
    apply (f2 T U V d0 (F T U d0) d1 (F U V d1)).
    firstorder.
    firstorder.
    firstorder.
    
  destruct b1,b2; simpl in *.
    apply (f3 T V p d0 (F T V d0) d1 (F T V d1)).
    firstorder.
    firstorder.
    firstorder.

  destruct b0; simpl in *.
    apply (f4 T p d0 (F T T d0)).
    firstorder.
    firstorder.

  destruct b0; simpl in *.
    apply ( f6 T V p d0 (F T V d0)).
    firstorder.

  destruct b1,b2; simpl in *.
    apply (f7 T V d0 (F T V d0) d1 (F T V d1)).
    firstorder.
    firstorder.
    firstorder.
Qed.

Lemma s2d_stmt_eq : forall T V (Q : @Statement.Stmt T V), π1 (s2d Q) = Q.
Proof.
  intros.
  induction Q; simpl in *; auto.
  { rewrite IHQ1, IHQ2; auto. }
  { rewrite IHQ1, IHQ2; auto. }
  { rewrite IHQ; auto. }
  { rewrite IHQ; auto. }
  { rewrite IHQ1, IHQ2; auto. }
Qed.

Lemma design_stmt_iso : forall T V (d : @Dev T V true) (s : @Stmt T V), s2d s = d <-> s = π1 d.
Proof.
  intros T V d s.
  split.
  { destruct s; intros; simpl in *; subst d; simpl; 
    repeat rewrite s2d_stmt_eq; auto.
  }
  { intros; subst s.
    pattern T,V,d.
    apply (Dev_ind_true); simpl in *; clear; auto.
    intros; rewrite H,H0; auto.
    intros; rewrite H,H0; auto.
    intros; rewrite H; auto.
    intros; rewrite H; auto.
    intros; rewrite H,H0; auto.
  }
Qed.

Theorem completeness :
  forall T V (P : @Statement.Stmt T V) (Q : T >> V),
    P ⊑ ⟨Q⟩ -> exists (d : @Dev T V false), (φ d) = (⟨Q⟩,P) /\ CbC d.
Proof.
  intros T V P.
  induction P; intros.
  { exists (Block (Spec Q) (s2d Statement.Void)); simpl.
    split; auto.
    apply (CDBlock (CDSpec Q)  CDVoid H).
  }
  { exists (Block (Spec Q) (Assignment e)); simpl.
    split; auto.
    apply (CDBlock (CDSpec Q) (CDAssignment e) H).
  }
  { destruct (IHP1 _ (refines_reflexive _ _ _)) as (d1,(HHEq1,HHcbc1)).
    destruct (IHP2 _ (refines_reflexive _ _ _)) as (d2,(HHEq2,HHcbc2)).
    exists (Block (Spec Q) (Seq d1 d2)); simpl.
    split.
    { destruct (dsem d1),(dsem d2); simpl in *.
      inversion HHEq1; inversion HHEq2; subst; auto.
    }
    { apply (CDBlock (CDSpec Q) (CDSeq HHcbc1 HHcbc2)); simpl.
      simpl in *.
      destruct (dsem d1),(dsem d2); simpl in *.
      inversion HHEq1; inversion HHEq2; subst.
      auto.
    }
  }
  { destruct (IHP1 _ (refines_reflexive _ _ _)) as (d1,(HHEq1,HHcbc1)).
    destruct (IHP2 _ (refines_reflexive _ _ _)) as (d2,(HHEq2,HHcbc2)).
    exists (Block (Spec Q) (If p d1 d2)); simpl.
    split.
    { destruct (dsem d1),(dsem d2); simpl in *.
      inversion HHEq1; inversion HHEq2; subst; auto.
    }
    { apply (CDBlock (CDSpec Q) (CDIf p HHcbc1 HHcbc2)).
      simpl; destruct (dsem d1),(dsem d2); simpl in *.
      inversion HHEq1; inversion HHEq2; subst; auto.
    }
  }
  { pose proof H as H'.
    rewrite while_rule_sound_and_complete in H'.
    destruct H' as (K,(HHpk,HHk)).
    destruct (IHP _ HHpk) as (d,(HHEq,HHcbc)).
    exists (Block (Spec Q) (While p d)).
    split.
    { simpl.
      destruct (dsem d).
      inversion HHEq; subst.
      auto.
    }
    {  destruct HHk as (HHk,(HHk1,HHk2)).
       constructor.
       { constructor; auto. }
       { constructor; destruct (dsem d); simpl; inversion HHEq; subst; simpl in *; auto.
         rewrite <- loop_body_refines_equiv; auto.
       }
       { simpl.
         destruct (dsem d); simpl.
         inversion_clear HHEq.
         assert (pred K = (pred ⟨pred K⟩)) by auto.
         rewrite H0 in HHk2.
         unshelve eapply (refines_trans _ _ _ _ _ _ HHk2).
         apply wfd_while_refines_if; auto.
       }
    }
  }
  { exists (Block (Spec Q) (Spec s)); simpl.
    split; auto.
    { apply (CDBlock (CDSpec Q) (CDSpec s)); simpl.
      auto.
    }
  }
  { simpl.
    pose proof (IHP (pred P) (refines_reflexive _ _ _)).
    destruct H0.
    destruct H0.
    simpl in H0.
    exists (Block (Spec Q) (Guarded p x)); simpl.
    split.
    { destruct (dsem _); inversion H0; subst; simpl; auto.
    }
    { constructor; simpl.
      { constructor; auto. }
      { constructor; auto. }
      { destruct (dsem _); inversion H0; subst; simpl; auto.
      }
    }
  }
  { destruct (IHP1 _ (refines_reflexive _ _ _)) as (d1,(HHEq1,HHcbc1)).
    destruct (IHP2 _ (refines_reflexive _ _ _)) as (d2,(HHEq2,HHcbc2)).
    exists (Block (Spec Q) (Choice d1 d2)); simpl.
    split.
    { destruct (dsem d1),(dsem d2); inversion HHEq1; inversion HHEq2; subst; auto.
    }
    { apply (CDBlock (CDSpec _) (CDChoice HHcbc1 HHcbc2)).
      simpl; destruct (dsem d1),(dsem d2); inversion HHEq1; inversion HHEq2; subst; simpl; auto.
    }
  }
Qed.

Require Import Wpr Predicative.

Fixpoint wpr' { T U V : Type } { b } (D : @Dev U V b) (S : T >> V) : T >> U :=
  match D (*in (@Dev _ VV _) return (forall (S : T >> VV), T >> U)*) with
  | Void => fun S => wpr Statement.Void S
  | Spec S1 => fun S => wpr (Statement.Spec S1) S
  | Assignment f => fun S => wpr (Statement.Assignment f) S
  | Seq C1 C2 => fun S => wpr' C1 (wpr' C2 S)
  | If p Ct Cf => fun S s s' => (p s' /\ wpr' Ct S s s') \/ (~ p s' /\ wpr' Cf S s s')
  | While p C => fun S s s' => p s' /\ wpr' C (fun s s' => ~ p s' -> S s s') s s' \/ ~ p s' /\ S s s'
  | Block S1 D1 => fun S => wpr' S1 S
  | Guarded p C => fun S s s' => (p s' /\ wpr' C S s s')
  | Choice C1 C2 => fun S s s' => wpr' C1 S s s' /\ wpr' C2 S s s'
  end S.

Theorem wpr_wpr' : forall {T U V b} {d : @Dev U V b}, CbC d -> forall (S : T >> V) s s', wpr (π1 d) S s s' <-> wpr' d S s s'.
Proof.
  intros T U V b d HHd.
  induction HHd; try reflexivity.
  { simpl; setoid_rewrite <- IHHHd1.
    setoid_rewrite <- wpr_pred.
    intros S.
    apply Wpr.right_extensionality.
    auto.
  }
  { simpl. setoid_rewrite IHHHd1; setoid_rewrite IHHHd2; reflexivity. }
  { simpl (dsem _); simpl (fst _).
    intros S s s'.    
    setoid_rewrite wpr_while_wpr_if'; auto.
    { simpl.
      rewrite IHHHd.
      clear; firstorder.
    }
    { apply loop_body_refines_equiv.
      auto.
    }
  }
  { simpl. setoid_rewrite IHHHd1; reflexivity. }
  { simpl. setoid_rewrite IHHHd; reflexivity. }
  { simpl; setoid_rewrite IHHHd1; setoid_rewrite IHHHd2; reflexivity. }
Qed.

Theorem wpr'_refines :
  forall {T U b} {d : @Dev T U b} S,
    CbC d
    -> (forall s, (exists s', pred S s s') -> wpr' d (pred S) s s) <-> ((π1 d) ⊑ S).
Proof.
  intros.
  setoid_rewrite <- wpr_wpr'; auto.
  rewrite wpr_refines.
  reflexivity.
Qed.

Theorem refines_if_wpr' :
  forall {T U b} {d : @Dev T U b} S,
    CbC d
    -> (forall s, (exists s', pred S s s') -> wpr' d (pred S) s s) -> ((π1 d) ⊑ S).
Proof.  intros; apply wpr'_refines; auto. Qed.

Definition cond2stmt { T } (C : @Predicate T) := Statement.Guarded C (@Skip T).

Fixpoint cd2d { T V b } { d : @Dev T V b } (cd : CbC d) := d. 
  
Close Scope stmt_scope.

Definition build_cd_block
  { T U b} { spec : @Dev T U true } { impl }
  (cdspec : @CbC T U true spec)
  (cdimpl : @CbC T U b  impl)
  (proof : let S := (π1 spec) in (forall s, (exists s', pred S s s') -> wpr' impl (pred S) s s))
  := CDBlock cdspec cdimpl (refines_if_wpr' _ cdimpl proof).

Definition build_cd_while
  { T b} { d : @Dev T T b }
  (p : @Predicate T)
  (cd : @CbC T T b d)
  (proof_wf :  well_founded (fun s s' => p s' /\ pred (π1 d) s' s /\ p s))
  (proof_body :   (let K := If p d (Assignment (fun s => s)) in (forall s, (exists s', pred (π1 K) s s') -> wpr' (Seq K K) (pred (π1 K)) s s)))
  := CDWhile p cd proof_wf (refines_if_wpr' _  (let CDK := CDIf p cd (CDAssignment (fun s => s)) in CDSeq CDK CDK) proof_body).

Definition CbCSpec { T V b } { D : @Dev T V b } ( _ : CbC D) := π1 D.
Definition CbCImpl { T V b } { D : @Dev T V b } ( _ : CbC D) := π2 D.
Notation "'Π1' D" := (CbCSpec D) (at level 70) : cbc_scope.
Notation "'Π2' D" := (CbCImpl D) (at level 70) : cbc_scope.


Notation "'Fail'" := (CDVoid) (at level 89) : cbc_scope.
Notation "'Skip'" := (CDAssignment (fun s => s)) (at level 89) : cbc_scope.
Notation "' x := e" := (CDAssignment (fun x => e)) (at level 30, x pattern at level 50, format "' x  :=  e") : cbc_scope.
Notation "⟨ spec ⟩" := (CDSpec spec) (at level 0) : cbc_scope.
Notation "'If' p 'Then' ct 'Else' cf 'End'" :=
  (CDIf p ct cf) (at level 90,  format "'[v' If  p   Then '/'  ct '/' Else '/'  cf '/' End ']'") : cbc_scope.
Notation "spec :{ impl }" := (build_cd_block spec impl _) (*(@CDBlock _ _ _ (cd2d spec) _ _ impl _)*)  (at level 50) : cbc_scope.
Notation "'When' p 'Then' c 'End'" := (@CDGuarded _ _ p _ c) (at level 50, format "'[v' When  p  Then '/'  c '/' End ']'") : cbc_scope.
Notation "'While' p 'Do' c 'Done'" := (build_cd_while p c _ _) (at level 50, format "'[v' While  p  Do '/'  c '/' Done ']'") : cbc_scope.
Notation "d1 ; d2" := (CDSeq d1 d2) (at level 51, right associativity) : cbc_scope.
Notation "d1 ⫾ d2" := (@CDChoice _ _ _ _ d1 d2) (at level 51, format "'[v' d1 ⫾ '/' d2 ']'", right associativity) : stmt_scope.

Bind Scope cbc_scope with CbC.



Open Scope cbc_scope.

Notation "'If' p 'Then' ct 'End'" := (If p Then ct Else Skip End)
                                       (at level 90,  format "'[v' If p  Then '/' ct '/' End ']'") : cbc_scope.

Close Scope cbc_scope.

Obligation Tactic := match goal with | _ => simpl end.

Notation "C1 ⊑ C2" := (Predicative.refines C1 C2) (at level 60, format "C1  ⊑  C2").
