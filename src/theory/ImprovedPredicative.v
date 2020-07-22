Require Import Decidable.

Require Import Predicate DemonicComposition DemonicJoin Specification Statement LeastFixpoint Predicative.

Open Scope stmt_scope.

Definition old_pred { T V : Type } := @pred T V.

Fixpoint  pred_seq { T U V: Type } (C : @Stmt T U) (spec : U >> V)
: T >> V :=
  match C in (@Stmt _ UU) return (forall (spec : UU >> V), T >> V) with
  | Void => fun spec s s' => False
  | Assignment effect => fun spec (s : T) (s' : V) => spec (effect s) s'
  | Seq cb ca => fun spec => pred_seq cb (pred_seq ca spec)                                   
  | If p ct cf => fun spec s s' => (p s /\ pred_seq ct spec s s') \/ (~ p s /\ pred_seq cf spec s s')
  | While p cw => fun spec => (while p (pred_seq cw (fun s s' => s = s'))) ⊟ spec
  | Spec call_spec => fun spec => call_spec ⊟ spec
  | WWhen p Then cw End => fun spec s s' => (p s /\ pred_seq cw spec s s')
  | c1 ⫾ c2 => fun spec => (pred_seq c1 spec) ⊔ (pred_seq c2 spec)
  end spec.

Fixpoint pred_opt { T V : Type } (C : @Stmt T V) : T >> V :=
  match C with
  | Void => fun s s' => False
  | Assignment effect => fun s s' => effect s = s'
  | Seq c1 c2 => pred_seq c1 (pred_opt c2)
  | If p ct cf => fun s s' => (p s /\ pred_opt ct s s') \/ (~ p s /\ pred_opt cf s s')
  | While p c => while p (pred_opt c) 
  | Spec spec => spec
  | WWhen p Then cw End => fun s s' => (p s /\ pred_opt cw s s')
  | c1 ⫾ c2 => (pred_opt c1) ⊔ (pred_opt c2)
  end.

Lemma pred_opt_pred_seq : forall { T U : Type } (c1 : @Stmt T U) V (c2 : @Stmt U V) s s',
    pred_seq c1 (pred_opt c2) s s' <-> ((pred_opt c1) ⊟ (pred_opt c2)) s s'.
Proof.
  intros T U c1.
  induction c1 as [ | T U effect | T U1 U2 cc1 IHcc1 cc2 IHcc2 | T U p ct IHct cf IHcf | T p cw IHcw | T call_spec | | ]; simpl.
 { intros c2 s s'; split; intros HH.
    { contradiction. }
    { destruct HH as [[sx [HH _]] _ ]; auto. }
  }
  { intros V c2 s s';  split; intros HH.
    { split.
      { exists (effect s); auto. }
      { intros sx HH1; subst sx; eauto. }
    }
    { destruct HH as [[sx [HHeql HHpred]] HH]; rewrite HHeql; exact HHpred. }
  }
  { intros V c2 s s'.
    rewrite (DemonicComposition.left_extensionality _ _ _ (IHcc1 _ _)).
    rewrite (IHcc1 _ (Statement.Seq cc2 c2)); simpl.
    rewrite (DemonicComposition.right_extensionality _ _ _ (IHcc2 _ _)).
    split; intros HH; apply DemonicComposition.assoc; auto.
  }
  { intros V c2 s s'; rewrite (IHcf _ _), (IHct _ _).
    split.
    { intros [ [HH1 [[sx [HH2 HH3]] HH4]] | [HH1 [[sx [HH2 HH3]] HH4]] ].
      { split; firstorder. }
      { split.
        { exists sx; split; auto. }
        { firstorder. }
      }
    }
    { intros [[sx [[[HH1 HH2] | [HH1 HH2]] HH3]] HH4].
      { left; split; auto; split; firstorder. }
      { right; split; auto; split; firstorder. }
    }
  }
  { intros V c2 s s'; apply DemonicComposition.left_extensionality.
    intros r r'. apply while_extensionality.
    { reflexivity. }
    { clear s s' r r'; intros.
      rewrite (IHcw _ (Spec (fun s s' => s = s'))); simpl.
      rewrite DemonicComposition.right_identity_neutrality.
      reflexivity.
    }
  }
  { reflexivity. }
  { intros; rewrite IHc1; simpl.
    firstorder.
  }
  { intros.
    rewrite DemonicComposition.ldistr_join.
    apply DemonicJoin.ext; auto.
  }
Qed.

Theorem pred_opt_IFF_old_pred : forall { T V : Type } (c : @Stmt T V) s s', old_pred c s s' <-> pred_opt c s s'.
Proof.
  induction c as [ | T U effect | T U1 U2 c1 IHc1 c2 IHc2 | T U p ct IHct cf IHcf | T p cw IHcw | T call_spec | | ]
  ; simpl; try reflexivity.
  { intros s s'; split; intros HHpred.
    { destruct HHpred as [[sx [HHpred1 HHpred2]] HHpred3].
      apply pred_opt_pred_seq; split.
      { exists sx; split; firstorder. }
      { intros sy HH1.
        rewrite <- (IHc1 _) in HH1.
        destruct (HHpred3 _ HH1) as (sy',HH2).
        exists sy'; apply IHc2; auto.
      }
    }
    { apply pred_opt_pred_seq in HHpred.
      apply (DemonicComposition.extensionality _ _ _ _ IHc1 IHc2); auto.
    }
  }
  { intros s s'; rewrite IHct,IHcf; reflexivity. }
  { apply while_extensionality; auto; reflexivity. }
  { intros; rewrite IHc; firstorder. }
  { intros; apply DemonicJoin.ext; auto. }
Qed.

Definition old_while { T : Type } := @Predicative.while T.

Definition while { T : Type } (C : @Predicate T) P := lfp (fun X s s' => (C s /\ pred_seq P X s s') \/ (~ C s /\ s = s')).

Theorem old_while_while : forall { T : Type } (C : @Predicate T) P s s', old_while C (pred_opt P) s s' <-> while C P s s'.
Proof.
  intros S C P s s'.
  unfold old_while,while,while_functional.
  apply lfp_extensionality.
  clear s s'; intros X s s'.
  rewrite (pred_opt_pred_seq _ _ (Spec X)).
  simpl.
  reflexivity.
Qed.

Fixpoint pred { T V : Type } (C : @Stmt T V) : Specification :=
  match C with
  | Void => fun s s' => False
  | Assignment effect => fun s s' => effect s = s'
  | Seq c1 c2 => pred_seq c1 (pred_opt c2)
  | If p ct cf => fun s s' => (p s /\ pred_opt ct s s') \/ (~ p s /\ pred_opt cf s s')
  | While p c => while p c 
  | Spec spec => spec
  | WWhen p Then cw End => fun s s' => (p s /\ pred_opt cw s s')
  | c1 ⫾ c2 => (pred_opt c1) ⊔ (pred_opt c2)
  end.

Lemma pred_pred_opt : forall { T V : Type } (C : @Stmt T V), forall s s', pred C s s' <-> pred_opt C s s'.
Proof.
  intros T V C s s'.
  destruct C; simpl in *; try reflexivity.
  rewrite old_while_while.
  reflexivity.
Qed.

Theorem pred_old_pred : forall { T V : Type } (C : @Stmt T V), forall s s', pred C s s' <-> old_pred C s s'.
  intros T V C s s'.
  apply (iff_trans (pred_pred_opt C s s')).
  apply iff_sym.
  apply pred_opt_IFF_old_pred.
Qed.

Theorem while_end : forall (T V : Type) (C : @Predicate T) P s s', while C P s s' -> ~ C s'.
Proof.
  intros T V C P s s'.
  rewrite <- old_while_while.
  apply Predicative.while_end.
Qed.

Theorem while_destruct : forall { T : Type } (C : @Predicate T) P s s',
    while C P s s' -> (C s /\ (pred_seq P (while C P)) s s') \/ (~ C s /\ s = s').
Proof.
  intros T C P s s'.
  rewrite <- old_while_while.
  rewrite (pred_opt_pred_seq P _ (Statement.Spec (while C P))); simpl.
  rewrite (DemonicComposition.extensionality (pred_opt P) (pred_opt P) (while C P) (old_while C (pred_opt P))); try reflexivity.
  { apply Predicative.while_destruct. }
  { clear s s'.
    intros s s'; rewrite old_while_while; reflexivity.
  }
Qed.

Theorem while_construct : forall { T : Type } (C : @Predicate T) P s s',
    (C s /\ (pred_seq P (while C P)) s s') \/ (~ C s /\ s = s') -> while C P s s'.
Proof.
  intros T C P s s'.
  rewrite <- old_while_while.
  rewrite (pred_opt_pred_seq P _ (Statement.Spec (while C P))); simpl.
  rewrite (DemonicComposition.extensionality (pred_opt P) (pred_opt P) (while C P) (old_while C (pred_opt P))); try reflexivity.
  { apply Predicative.while_construct. }
  { clear s s'.
    intros s s'; rewrite old_while_while; reflexivity.
  }
Qed.

Theorem while_fix : forall { T : Type } (C : @Predicate T) P s s', while C P s s' <-> (C s /\ (pred_seq P (while C P)) s s') \/ (~ C s /\ s = s').
Proof.
  intros T C P s s'.
  rewrite <- old_while_while.
  rewrite (pred_opt_pred_seq P _ (Statement.Spec (while C P))); simpl.
  rewrite (DemonicComposition.extensionality (pred_opt P) (pred_opt P) (while C P) (old_while C (pred_opt P))); try reflexivity.
  { apply Predicative.while_fix. }
  { clear s s'.
    intros s s'; rewrite old_while_while; reflexivity.
  }
Qed.

Theorem while_ind : forall { T : Type } (C : @Predicate T) P X s s',
    while C P s s' -> (forall s s', ((C s /\ (pred_seq P X) s s') \/ (~ C s /\ s = s')) -> X s s') -> X s s'.
Proof.
  intros T C P X s s' HHwhile HH.
  eapply (f_lfp _ _ _ _ _ HHwhile).
  Unshelve.
  auto.
Qed.

Theorem ex_while_ind : forall { T : Type } (C : @Predicate T) P (X : Predicate) s,
    (exists s', while C P s s') -> (forall s, ((C s /\ (forall sx, (pred P s sx -> X sx)) \/ (~ C s)) -> X s)) -> X s.
Proof.
  intros T C P X s (s',HHwhile).
  pattern s,s'; apply HHwhile.
  intros.
  apply H0.
  destruct H.
  { destruct H. left; split; auto.
    rewrite (pred_opt_pred_seq
               P _ (Statement.Spec (fun s _ : T => (forall s1 : T, C s1 /\ (forall sx : T, pred P s1 sx -> X sx) \/ ~ C s1 -> X s1) -> X s))) in H1.
    destruct H1.
    intros.
    rewrite pred_pred_opt in H3.
    destruct (H2 _ H3).
    apply H4.
    auto. 
  }
  { right; firstorder. }
Qed.

Theorem while_well_founded : forall { T : Type } (p : @Predicate T) C,
    well_founded (fun s s' => p s' /\ (pred C) s' s /\ (exists r, (while p C) s' r)).
Proof.
  intros T p C.
  constructor. 
  intros y [HHp [HHpred HHwhile]].
  generalize y HHp HHpred; clear y HHp HHpred.
  pattern a; apply (ex_while_ind _ _ _ _ HHwhile).
  intros.
  destruct H; try contradiction.
  destruct H.
  constructor; intros.
  destruct H1.
  destruct H2.
  apply (H0 y); auto.
Qed.

Lemma wfd_prefix_while : forall { T : Type } (C : @Predicate T) P (K : Specification),
    well_founded (fun s s' => C s' /\ pred P s' s)
    -> (forall s s', K s s' -> ((C s /\ pred_seq P K s s') \/ (~ C s /\ s = s')))
    -> forall s s', K s s' -> while C P s s'.
Proof.
  intros T C P K HHwfd HHT1 s.
  pattern s; apply (well_founded_ind HHwfd).
  intros sx HH s' HHT.
  pose proof (HHT1 _ _ HHT).
  rewrite (pred_opt_pred_seq _ _ (Statement.Spec K)) in H.
  destruct H as [(HHc,((sy,(HH11,HH12)),HH13)) | HH2]; simpl in *.
  { apply while_construct; left; split; auto.
    rewrite (pred_opt_pred_seq _ _ (Statement.Spec (while C P))).
    split; simpl; auto.
    { exists sy; split; auto.
      apply HH; auto; split; auto.
      apply pred_pred_opt; auto.
    }
    { intros sz HHp2.
      pose proof (HH13 _ HHp2) as (sz',HHT2).
      exists sz'.
      apply HH; auto; split; auto.
      apply pred_pred_opt; auto.
    }
  }
  { apply while_construct; right; auto. }
Qed.

Theorem wfd_fix_while : forall { T : Type } (C : @Predicate T) P (K : Specification),
    well_founded (fun s s' => C s' /\ pred P s' s)
    -> (forall s s', K s s' <-> ((C s /\ pred_seq P K s s') \/ (~ C s /\ s = s')))
    -> forall s s', while C P s s' <-> K s s'.
Proof.
  intros T C P K HHwfd HHT s s'.
  split.
  { intros HHwhile.
    apply (while_ind _ _ _ _ _ HHwhile).
    apply HHT.
  }
  { apply wfd_prefix_while; auto.
    apply HHT.
  }
Qed.


Theorem while_extensionality :
  forall { T : Type } (C1 : @Predicate T) P1 C2 P2,
    (forall s, C1 s <-> C2 s) -> (forall s s', pred P1 s s' <-> pred P2 s s') -> forall s s', while C1 P1 s s' <-> while C2 P2 s s'.
Proof.
  intros T C1 P1 C2 P2 HHequiv1 HHequiv2 s s'.
  assert ( forall s s' : T, pred_opt P1 s s' <-> pred_opt P2 s s') as HHequiv2'.
  { clear HHequiv1 s s'.
    intros s s'.
    repeat rewrite <- pred_pred_opt.
    auto.
  }
  clear HHequiv2.
  unfold while.
  apply lfp_extensionality.
  clear s s'.
  unfold while_functional.
  intros X s s'.
  rewrite HHequiv1.
  repeat rewrite (pred_opt_pred_seq _ _ (Statement.Spec X)).
  rewrite (DemonicComposition.left_extensionality _ _ _ HHequiv2').
  reflexivity.
Qed. 

Definition old_refines { T V : Type } := @refines T V.

Definition refines { T V : Type } (S1 S2 : @Stmt T V) :=
  forall s, (exists s', pred S2 s s') -> (forall s', pred S1 s s' -> pred S2 s s') /\ (exists s', pred S1 s s').

Lemma refines_old_refines : forall T V (C1 C2 : @Stmt T V), old_refines C1 C2 <-> refines C1 C2.
Proof.
  unfold old_refines, refines.
  intros S C1 C2.
  split; intros HHrefines.
  { intros s (t',HHc2).
    apply pred_old_pred in HHc2.
    destruct (HHrefines _ (ex_intro _ _ HHc2)) as (HHc1c2,(u',HHc1)).
    split.
    { intros s'; repeat rewrite pred_old_pred; apply HHc1c2. }
    { exists u'; rewrite pred_old_pred; exact HHc1. }
  }
  { intros s (t',HHc2).
    apply pred_old_pred in HHc2.
    destruct (HHrefines _ (ex_intro _ _ HHc2)) as (HHc1c2,(u',HHc1)).
    split.
    { intros s'; repeat rewrite <- pred_old_pred; apply HHc1c2. }
    { exists u'; rewrite <- pred_old_pred; exact HHc1. }
  }
Qed.

Notation "C1 ⊑ C2" := (refines C1 C2) (at level 60, format "C1  ⊑  C2").

Theorem if_extensionality :
  forall { T : Type } (C1 : @Predicate T) (P1 : @Stmt T T) C2 (P2 : @Stmt T T),
    (forall s, C1 s <-> C2 s) -> (forall s s', pred P1 s s' <-> pred P2 s s') -> forall s s', pred (IIf C1 Then P1 End) s s' <-> pred (IIf C2 Then P2 End) s s'.

Proof.
  intros T C1 P1 C2 P2 HHequiv1 HHequiv2 s s'.
  simpl. repeat rewrite <- pred_pred_opt.
  rewrite HHequiv1,HHequiv2.
  reflexivity.
Qed.

Theorem wfd_while_iff_if : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> forall s s', while C P s s' <-> pred (IIf C Then P End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHrefines s s'.
  rewrite <- old_while_while.
  rewrite <- (Predicative.while_extensionality C (pred P) C (pred_opt P)); try reflexivity.
  { rewrite <- (if_extensionality C ⟨pred P⟩ C ); try reflexivity.
    apply Predicative.wfd_while_iff_if; auto.
  }
  { apply pred_pred_opt. }
Qed.

Theorem wfd_while_iff_if' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> pred P s sx)
               /\ (C s' /\ (exists sx, pred P s' sx) \/ ~ C s'))
    -> forall s s', while C P s s' <-> pred (IIf C Then P End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHrefines s s'.
  rewrite <- old_while_while.
  rewrite <- (Predicative.while_extensionality C (pred P) C (pred_opt P)); try reflexivity.
  { rewrite <- (if_extensionality C ⟨pred P⟩ C ); try reflexivity.
    apply Predicative.wfd_while_iff_if'; simpl; auto; apply HHrefines.
  }
  { apply pred_pred_opt. }
Qed.

Theorem wfd_while_refines_if : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros * HHwfd HHrefines.
  unfold refines; simpl.
  intros * (s'',HHtrm).
  split.
  { intros s'.
    rewrite (wfd_while_iff_if _ _ HHwfd HHrefines).
    simpl.
    rewrite <- pred_pred_opt.
    clear.
    firstorder.
  }
  { exists s''.
    rewrite (wfd_while_iff_if _ _ HHwfd HHrefines).
    simpl.
    rewrite <- pred_pred_opt.
    destruct HHtrm.
    { firstorder. }
    { destruct H; subst s''; firstorder. }
  }
Qed.

Theorem wfd_while_refines_if' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> pred P s sx)
               /\ (C s' /\ (exists sx, pred P s' sx) \/ ~ C s'))
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros * HHwfd HHrefines.
  unfold refines; simpl.
  intros * (s'',HHtrm).
  split.
  { intros s'.
    rewrite (wfd_while_iff_if' _ _ HHwfd HHrefines).
    simpl.
    rewrite <- pred_pred_opt.
    clear.
    firstorder.
  }
  { exists s''.
    rewrite (wfd_while_iff_if' _ _ HHwfd HHrefines).
    simpl.
    rewrite <- pred_pred_opt.
    destruct HHtrm.
    { firstorder. }
    { destruct H; subst s''; firstorder. }
  }
Qed.

Theorem if_refines_wfd_while : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End ⊑ WWhile C Do P Done.
Proof.
  intros * HHwfd HHrefines.
  unfold refines; simpl.
  intros * (s'',HHtrm).
  split.
  { intros s'.
    rewrite (wfd_while_iff_if _ _ HHwfd HHrefines).
    simpl.
    rewrite <- pred_pred_opt.
    intros [HHpred | HHskip].
    { firstorder. }
    { destruct HHskip; subst s'.
      clear - H. 
      firstorder.
    }
  }
  { exists s''.
    rewrite (wfd_while_iff_if _ _ HHwfd HHrefines) in HHtrm.
    simpl in HHtrm.
    rewrite <- pred_pred_opt in HHtrm.
    destruct HHtrm as ([ HHtrm | (HHc,HHeq) ], HHc').
    { firstorder. }
    { subst s''; firstorder. }
  }
Qed.

Require Import Wfd.

Theorem while_rule_sound_and_complete : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    <-> exists K, P ⊑ K
           /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
           /\ (⟨fun s s' => C s /\ pred K s s'⟩;⟨fun s s' => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred K s s'⟩
           /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros *.
  repeat setoid_rewrite <- refines_old_refines.
  split; intros.
  { apply while_rule_sound_and_complete in H.
    unfold old_refines in *; simpl.
    destruct H as (K,(H1,(H2,(H3,H4)))).
    exists K.
    split.
    { auto. }
    { split.
      { apply (Wfd.by_inclusion _ _ _ H2).
        setoid_rewrite pred_old_pred; unfold old_pred; simpl.
        auto.
      }
      { unfold Predicative.refines in *; simpl in *.
        unfold DemonicComposition.fn in *.
        repeat setoid_rewrite (pred_old_pred K); unfold old_pred.
        auto.
      }
    }
  }
  { apply while_rule_sound_and_complete.
    unfold old_refines in *; simpl.
    destruct H as (K,(H1,(H2,H3))).
    exists K.
    split; auto.
    { split.
      { apply (Wfd.by_inclusion _ _ _ H2).
        setoid_rewrite pred_old_pred; unfold old_pred; simpl.
        auto.
      }
      { unfold Predicative.refines in *; simpl in *.
        unfold DemonicComposition.fn in *.
        repeat setoid_rewrite (pred_old_pred K) in H3; unfold old_pred.
        auto.
      }
    }
  }
Qed.

Theorem refines_reflexive : forall (T V : Type)  (P : @Stmt T V), refines P P.
Proof.
  intros T V P.
  rewrite <- refines_old_refines.
  apply refines_reflexive.
Qed.

Theorem refines_trans : forall (T V : Type)  (P Q R : @Stmt T V), refines P Q -> refines Q R -> refines P R.
Proof.
  intros T V P Q R.
  repeat rewrite <- refines_old_refines.
  apply refines_trans.
Qed.

Theorem Seq_left_monotonic_refines :
  forall (T U V : Type) (P1 P2 : @Stmt T U) (Q : @Stmt U V), refines P1 P2 -> refines (Seq P1 Q) (Seq P2 Q).
Proof.
  intros T U V P1 P2 Q.
  repeat rewrite <- refines_old_refines.
  apply Seq_left_monotonic_refines.
Qed.

Theorem Seq_right_monotonic_refines :
  forall (T U V : Type) (P : @Stmt T U) (Q1 Q2 : @Stmt U V), refines Q1 Q2 -> refines (Seq P Q1) (Seq P Q2).
Proof.
  intros T U V P Q1 Q2.
  repeat rewrite <- refines_old_refines.
  apply Seq_right_monotonic_refines.
Qed.

Theorem Seq_monotonic_refines :
  forall (T U V : Type) (P1 : @Stmt T U) (P2 : @Stmt U V) (Q1 : @Stmt T U) (Q2 : @Stmt U V),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (Seq P1 P2) (Seq Q1 Q2).
Proof.
  intros T U V P1 P2 Q1 Q2.
  repeat rewrite <- refines_old_refines.
  apply Seq_monotonic_refines.
Qed.

Theorem If_monotonic_refines :
  forall (T V : Type) C (Pt Qt Pf Qf : @Stmt T V),
    refines Pt Qt
    -> refines Pf Qf
    -> refines (If C Pt Pf) (If C Qt Qf).
Proof.
  intros T V C Pt Pf Qt Qf.
  repeat rewrite <- refines_old_refines.
  apply If_monotonic_refines.
Qed.

Theorem When_monotonic_refines :
  forall (T V : Type) C (P Q : @Stmt T V),
    refines P Q
    -> refines (WWhen C Then P End) (WWhen C Then Q End).
Proof.
  intros T V C P Q.
  repeat rewrite <- refines_old_refines.
  apply When_monotonic_refines.
Qed.

Theorem Choice_left_monotonic_refines :
  forall (T V : Type) (P1 P2 : @Stmt T V) (Q : @Stmt T V), refines P1 P2 -> refines (P1 ⫾ Q) (P2 ⫾ Q).
Proof.
  intros *; repeat rewrite <- refines_old_refines.
  apply Choice_left_monotonic_refines.
Qed.

Theorem Choice_right_monotonic_refines :
  forall (T V : Type) (P : @Stmt T V) (Q1 Q2 : @Stmt T V), refines Q1 Q2 -> refines (P ⫾ Q1) (P ⫾ Q2).
Proof.
  intros *; repeat rewrite <- refines_old_refines.
  apply Choice_right_monotonic_refines.
Qed.

Theorem Choice_monotonic_refines :
  forall (T V : Type) (P1 Q1 : @Stmt T V) (P2 Q2 : @Stmt T V),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (P1 ⫾ P2) (Q1 ⫾ Q2).
Proof.
  intros *; repeat rewrite <- refines_old_refines.
  apply Choice_monotonic_refines.
Qed.

Theorem While_monotonic_refines :
  forall (T : Type) C (P Q : @Stmt T T),
    refines P Q
    -> refines (While C P) (While C Q).
Proof.
  intros T C P Q.
  repeat rewrite <- refines_old_refines.
  apply While_monotonic_refines.
Qed.

Theorem refines_extensionality_left : forall T V (P1 P2 Q : @Stmt T V), (forall s s', (pred P1) s s' <-> (pred P2) s s') -> refines P1 Q <-> refines P2 Q.
Proof.
  intros T V P1 P2 Q HHequiv.
  unfold refines; split.
  { intros HHsnd s HHq.
    split.
    { intros s''; rewrite <- HHequiv; apply (HHsnd _ HHq). }
    { destruct (HHsnd _ HHq) as (_,(s',HHp1)); exists s'; rewrite <- HHequiv; exact HHp1. }
  }
  { intros HHsnd s HHq.
    split.
    { intros s''; rewrite HHequiv; apply (HHsnd _ HHq). }
    { destruct (HHsnd _ HHq) as (_,(s',HHp2)); exists s'; rewrite HHequiv; exact HHp2. }
  }
Qed.

Theorem refines_extensionality_right : forall T V (P Q1 Q2 : @Stmt T V), (forall s s', (pred Q1) s s' <-> (pred Q2) s s') -> refines P Q1 <-> refines P Q2.
Proof.
  intros T V P Q1 Q2 HHequiv.
  unfold refines; split.
  { intros HHsnd s HHq.
    split.
    { intros s''; rewrite <- HHequiv; apply HHsnd.
      setoid_rewrite HHequiv; auto.
    }
    { apply HHsnd.
      setoid_rewrite HHequiv; auto.
    }
  }
  { intros HHsnd s HHq.
    split.
    { intros s''; rewrite HHequiv; apply HHsnd.
      setoid_rewrite <- HHequiv; auto.
    }
    { apply HHsnd; setoid_rewrite <- HHequiv; exact HHq. }
  }
Qed.

Theorem refines_extensionality : forall T V (P1 P2 Q1 Q2 : @Stmt T V),
    (forall s s', (pred P1) s s' <-> (pred P2) s s')
    -> (forall s s', (pred Q1) s s' <-> (pred Q2) s s')
    -> refines P1 Q1 <-> refines P2 Q2.
Proof.
  intros.
  assert (refines P1 Q1 <-> refines P1 Q2).
  { apply refines_extensionality_right; auto. }
  rewrite H1.
  apply refines_extensionality_left; auto.
Qed.

Close Scope stmt_scope.