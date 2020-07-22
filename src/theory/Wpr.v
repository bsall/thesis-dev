Require Import Predicate Specification DemonicComposition Statement LeastFixpoint Predicative.

Open Scope stmt_scope.

Definition wpr_spec { T U V : Type } (C : U >> V) (S : T >> V) : T >> U  := fun s s' => (forall sx, C s' sx -> S s sx) /\ (exists sx, C s' sx).

Definition wpo_spec { T U V : Type } (C : U >> V) (S : U >> T) : V >> T  := fun s' s => (forall sx, C sx s' -> S sx s) /\ (exists sx, C sx s').

Require Import AngelicComposition.

Theorem wpr_spec_and :  forall T U V (C : U >> V) (S1 S2 : T >> V) s s',
    wpr_spec C (fun s s' => S1 s s' /\ S2 s s') s s' <-> wpr_spec C S1 s s' /\  wpr_spec C S2 s s'.
Proof. firstorder. Qed.

Definition wpr_while { T V : Type } C (K : T >> V -> T >> V) (S : T >> V) :=
   fun s s' => forall (X: T >> V), (forall s s', (C s' /\ K X s s'  \/  ~ C s' /\ S s s') -> X s s') -> X s s'.

Fixpoint wpr { T U V : Type } (C : @Stmt U V) (S : T >> V) : T >> U :=
  match C in (@Stmt _ VV) return (forall (S : T >> VV), T >> U) with
  | Statement.Void => fun S s s' => False
  | Statement.Assignment effect => fun S s s' => S s (effect s')
  | Statement.Seq C1 C2 => fun S => wpr C1 (wpr C2 S)
  | Statement.If p Ct Cf => fun S s s' => (p s' /\ wpr Ct S s s') \/ (~ p s' /\ wpr Cf S s s')
  | Statement.While p C => fun S => wpr_while p (wpr C) S
  | Statement.Spec spec => fun S => wpr_spec spec S
  | Statement.Guarded p C => fun S s s' => (p s' /\ wpr C S s s')
  | C1 ⫾ C2 => fun S s s' => wpr C1 S s s' /\ wpr C2 S s s'
  end S.

Lemma wpr_monotonic_right : forall T U V (C : @Stmt U V) (S1 S2 : T >> V),
    (forall s s', S1 s s' -> S2 s s') -> forall s s', wpr C S1 s s' -> wpr C S2 s s'.
Proof. induction C; simpl in *; firstorder. Qed.

Definition wpr_while_functional { T U V : Type } C (P : @Stmt U V) (S : T >> U) (X : T >> V) s s' := C s' /\ wpr P X s s'  \/  ~ C s' /\ S s s'.


Lemma wpr_while_functional_monotonic :
  forall T U V C (P : @Stmt U V) (S : T >> U) (X1 X2 : T >> V),
    (forall s s', X1 s s' -> X2 s s') -> (forall s s', wpr_while_functional C P S X1 s s' -> wpr_while_functional C P S X2 s s').
Proof.
  intros T U V C P S T1 T2 HHT s s' [ (HHp,HHwpr) | HHwpr ].
  { left; split; auto; apply (wpr_monotonic_right _ _ _ _ _ _ HHT _ _ HHwpr). }
  { right; auto. }
Qed.

Theorem wpr_while_construct :
  forall T U C (P : @Stmt U U) (S : T >> U) s s',  C s' /\ wpr P (wpr (Statement.While C P) S) s s' \/ ~ C s' /\ S s s' -> wpr (Statement.While C P) S s s'.
Proof.
  intros T U C P S.
  apply (f_lfp_lfp (wpr_while_functional _ _ _) (wpr_while_functional_monotonic _ _ _ _ _ _)).
Qed.

Theorem wpr_while_destruct :
  forall T U C (P : @Stmt U U) (S : T >> U) s s', wpr (Statement.While C P) S s s' -> C s' /\ wpr P (wpr (Statement.While C P) S) s s' \/ ~ C s' /\ S s s' .
Proof.
  intros T U C P S.
  apply (lfp_f_lfp (wpr_while_functional _ _ _) (wpr_while_functional_monotonic _ _ _ _ _ _)).
Qed.

Theorem wpr_while_ind :
  forall T U C (P : @Stmt U U) (S : T >> U) X,
    (forall s s',  C s' /\ wpr P X s s'  \/  ~ C s' /\ S s s' -> X s s')
    -> forall s s', wpr (Statement.While C P) S s s' -> X s s'.
Proof.
  intros *.
  apply (f_lfp  (wpr_while_functional _ _ _)).
Qed.

Lemma right_monotonic :
  forall T U V (C : U >> V) (S1 S2 : T >> V), (forall s s', S1 s s' -> S2 s s') -> forall s s', wpr (Statement.Spec C) S1 s s' -> wpr (Statement.Spec C) S2 s s'.
Proof. firstorder. Qed.

Lemma right_extensionality :
  forall T U V (C : U >> V) (S1 S2 : T >> V), (forall s s', S1 s s' <-> S2 s s') -> forall s s', wpr (Statement.Spec C) S1 s s' <-> wpr (Statement.Spec C) S2 s s'.
Proof. firstorder. Qed.

Lemma left_extensionality :
  forall T U V (C1 C2 : U >> V) (S : T >> V),
    (forall s s', C1 s s' <-> C2 s s') -> forall s s', wpr (Statement.Spec C2) S s s' <-> wpr (Statement.Spec C1) S s s'.
Proof. firstorder. Qed.

Lemma wpr_pred : forall T U V (C : @Stmt U V) (S : T >> V) s s', wpr (Statement.Spec (pred C)) S s s' <-> wpr C S s s'.
Proof.
  induction C.
  { firstorder. }
  { simpl; intros S s s'; split.
    { intros (HHspec,_); apply HHspec; reflexivity. }
    { intros HHspec; split; eauto.
      intros sx HHeq; subst sx. exact HHspec.
    }
  }
  { simpl; intros S s s'; split.
    { intros HHpred.
      apply (IHC1); auto.
      apply (right_monotonic _ _ _ _ (wpr (Statement.Spec (pred C2)) S)).
      { intros r r'; apply IHC2; auto. }
      { firstorder. }
    }
    { intros HHwpr.
      apply IHC1 in HHwpr; auto. apply (right_monotonic _ _ _ _ _ (wpr (Statement.Spec (pred C2)) S)) in HHwpr.
      { simpl in HHwpr; firstorder. }
      { intros r r'; apply (IHC2 _ _ _); auto. }
    } 
  }
  { simpl; intros S s s'.
    split.
    { intros [HHpred1 [sx [(HHp,HHpred2) | (HHp,HHpred2)]]].
      { left; split; auto; apply IHC1; firstorder. }
      { right; split; auto; apply IHC2; firstorder. }
    }
    { intros [(HHp,HHwpr) | (HHp,HHwpr)].
      { apply IHC1 in HHwpr; firstorder. }
      { apply IHC2 in HHwpr; firstorder. }
    }
  }
  { intros S s s'.
    split.
    { generalize s; clear s.
      pattern s'; apply (well_founded_ind (while_well_founded p (pred C))).
      clear s'.
      intros s' HHwfdind s HHwpr.
      destruct HHwpr as (H1,H2).
      destruct H2 as (sx,H2); simpl in H2.
      pose proof H2 as H2'.
      apply while_destruct in H2. 
      destruct H2 as [ (HHps',((sy,(HH11,HH12)),HH2)) | (HHps',HH) ].
      { apply wpr_while_construct; left; split; auto.
        apply IHC; auto; split; eauto.
        intros sz HHpred.
        apply HHwfdind.
        { repeat split; auto.
          exists sx; apply while_construct; left; split; auto.
          split; eauto.
        }
        { simpl; split; eauto.
          intros sz' HHpred'.
          apply H1; simpl.
          apply while_construct; left; split; auto.
          split; eauto.
        }
      }
      { apply wpr_while_construct; right; split; auto.
        apply H1; apply while_construct; subst sx; auto.
      }
    }
    { apply (wpr_while_ind _ _ _ _ _); clear s s'.
      Transparent wpr.
      intros r r' [[HHp HHwpr] | [HHp HHwpr] ].
      { apply IHC in HHwpr; auto.
        destruct HHwpr as [HH1 (sx,HH2)].
        split.
        { intros sy HHpred; simpl in HHpred.
          pose proof HHpred as HHpred'.
          apply while_destruct in HHpred'.
          destruct HHpred' as [ (_,((sx',(HH31,HH32)),HH4)) | (HHp1,_) ]; try contradiction.
          apply (HH1 _ HH31).
          auto.
        }
        { destruct (HH1 _ HH2) as (HH3,(sx',HH4)).
          exists sx'; simpl; apply while_construct. left ; split; auto.
          split; eauto.
          intros sy HHpred.
          destruct (HH1 _ HHpred); eauto.
        }
      }
      { simpl; split.
        { intros sx HHwhile.
          apply while_destruct in HHwhile.
          destruct HHwhile as [ (HHpr',(HH1,HH2)) | (_,HHeq) ]; try contradiction.
          subst sx; exact HHwpr.
        }
        { exists r'; apply while_construct; right; auto. }
      }
    } 
  }
  { reflexivity. }
  { simpl.
    setoid_rewrite <- IHC.
    firstorder.
  }
  { simpl in *.
    intros.
    rewrite <- IHC1, <- IHC2.
    clear; firstorder.
  }
Qed.

Lemma wpr_seq : forall T U V (C :@Stmt U V) (S : T >> V), forall s sx, wpr C S s sx <-> ((forall s', pred C sx s' -> S s s') /\ exists s', pred C sx s').
Proof.
  intros T U V C S s sx.
  split.
  { intros HHwpr.
    apply wpr_pred in HHwpr; auto.
  }
  { intros HHpred.
    apply wpr_pred; auto.
  }
Qed.

Theorem wpr_refines : forall T V (C : @Stmt T V) (S : @Stmt T V), (forall s, (exists s', (pred S) s s') -> wpr C (pred S) s s) <-> refines C S.
Proof.
  intros. unfold refines; intros; split.
  { intros HHwpr s HHex; apply (wpr_seq _ _ _ C (pred S) s s); auto. }
  { intros HHpred s HHex; apply (wpr_seq _ _ _ C (pred S) s s); auto. }
Qed.

Theorem wpr_while_wpr_if' : forall  U V (C : @Predicate V) (P : @Stmt V V) (R : U >> V) s s',
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> Predicative.refines (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⟨fun s s' => C s /\ pred P s s'⟩
    -> wpr (WWhile C Do P Done) R s s' <-> wpr (IIf C Then P End) (fun s s' => ~ C s' -> R s s') s s'.
Proof.
  intros.
  rewrite <- (wpr_pred _ _ _ (Statement.While _ _)).
  rewrite <- (wpr_pred _ _ _ (Statement.If _ _ _)).
  simpl (Predicative.pred _).
  rewrite <- (left_extensionality _ _ _ _ _ _ (Predicative.wfd_while_iff_if _ _ H H0)).
  simpl.
  intros.
  split; intros.
  { 
    clear H0 H.
    unfold wpr_spec in *; simpl in *.
    destruct H1.
    split; auto.
    destruct H0 as (sx,(H01,H02)).
    eauto.
  }
  { clear -H H0 H1; unfold wpr_spec in *; simpl in *.
    destruct H1; split.
    { intros * [H3 H3']; auto. }
    { generalize H2; clear - H H0.
      pattern s'; apply (well_founded_ind H).
      clear H; intros. 
      destruct H2 as (sx,[H2 | H2]).
      { pose proof (H0 _ (ex_intro _ _ H2)).
        simpl in *.
        destruct H1.
        destruct H3 as (s'',(H31,H32)).
        destruct (H32 _ H2) as (sx',[H32' | H32']).
        { pose proof (H _ (match H2,H32' with (conj Ha Hb), (conj Hc _) => conj Ha (conj Hb Hc) end) (ex_intro _ _ (or_introl H32'))).
          destruct H3 as (sx0,([H3' | H3'],Hsx0)).
          { exists sx0; split; auto.
            left; apply H0; simpl; eauto.
            split; eauto.
          }
          { clear - H32' H3'; firstorder. }
        }
        { destruct H32'; subst; eauto. }
      }
      { exists sx; destruct H2; subst; auto. }
    }
  }
Qed.

Close Scope stmt_scope.

Require Import ImprovedPredicative.

Open Scope stmt_scope.

Definition refines { T V : Type } (P Q : @Stmt T V) :=
  (forall s, (exists s', (ImprovedPredicative.pred Q) s s') -> wpr P (ImprovedPredicative.pred Q) s s).


Theorem refines_predicative_refines : forall T V (P Q : @Stmt T V), refines P Q <-> Predicative.refines P Q.
Proof.
  intros T V P Q.
  rewrite <- (wpr_refines _ _ _).
  unfold refines.
  split.
  { intros HHrefines s (s',HHq).
    rewrite <- (wpr_pred _ _ _ _ _).
    apply (right_monotonic _ _ _ (Predicative.pred P) (ImprovedPredicative.pred Q) (Predicative.pred Q)).
    { apply pred_old_pred. }
    { rewrite (wpr_pred _ _ _ _ _).
      apply HHrefines.
      exists s'; apply pred_old_pred; exact HHq.
    }
  }
  { intros HHrefines s (s',HHq).
    rewrite <- (wpr_pred _ _ _ _ _).
    apply (right_monotonic _ _ _ (Predicative.pred P) (Predicative.pred Q) (ImprovedPredicative.pred Q)).
    { apply pred_old_pred. }
    { rewrite (wpr_pred _ _ _ _ _).
      apply HHrefines.
      exists s'; apply pred_old_pred; exact HHq.
    }
  }
Qed.

Notation "C1 ⊑ C2" := (refines C1 C2) (at level 60, format "C1  ⊑  C2").

Theorem refines_reflexive : forall (T V : Type)  (P : @Stmt T V), refines P P.
Proof.
  intros T V P.
  rewrite (refines_predicative_refines _ _ _).
  apply (Predicative.refines_reflexive _ _ P).
Qed.

Theorem refines_trans : forall (T V : Type)  (P Q R : @Stmt T V), refines P Q -> refines Q R -> refines P R.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply refines_trans.
Qed.

Theorem Seq_left_monotonic_refines :
  forall (T U V : Type) (P1 P2 : @Stmt T U) (Q : @Stmt U V), refines P1 P2 -> refines (Seq P1 Q) (Seq P2 Q).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Seq_left_monotonic_refines.
Qed.

Theorem Seq_right_monotonic_refines :
  forall (T U V : Type) (P : @Stmt T U) (Q1 Q2 : @Stmt U V), refines Q1 Q2 -> refines (Seq P Q1) (Seq P Q2).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Seq_right_monotonic_refines.
Qed.

Theorem Seq_monotonic_refines :
  forall (T U V : Type) (P1 : @Stmt T U) (P2 : @Stmt U V) (Q1 : @Stmt T U) (Q2 : @Stmt U V),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (Seq P1 P2) (Seq Q1 Q2).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Seq_monotonic_refines.
Qed.

Theorem If_monotonic_refines :
  forall (T V : Type) C (Pt Qt Pf Qf : @Stmt T V),
    refines Pt Qt
    -> refines Pf Qf
    -> refines (If C Pt Pf) (If C Qt Qf).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply If_monotonic_refines.
Qed.

Theorem When_monotonic_refines :
  forall (T V : Type) C (P Q : @Stmt T V),
    refines P Q
    -> refines (WWhen C Then P End) (WWhen C Then Q End).
Proof.
  intros T V C P Q.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply When_monotonic_refines.
Qed.

Theorem Choice_left_monotonic_refines :
  forall (T V : Type) (P1 P2 : @Stmt T V) (Q : @Stmt T V), refines P1 P2 -> refines (P1 ⫾ Q) (P2 ⫾ Q).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Choice_left_monotonic_refines.
Qed.

Theorem Choice_right_monotonic_refines :
  forall (T V : Type) (P : @Stmt T V) (Q1 Q2 : @Stmt T V), refines Q1 Q2 -> refines (P ⫾ Q1) (P ⫾ Q2).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Choice_right_monotonic_refines.
Qed.

Theorem Choice_monotonic_refines :
  forall (T V : Type) (P1 Q1 : @Stmt T V) (P2 Q2 : @Stmt T V),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (P1 ⫾ P2) (Q1 ⫾ Q2).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Choice_monotonic_refines.
Qed.

Theorem While_monotonic_refines :
  forall (T : Type) C (P Q : @Stmt T T),
    refines P Q
    -> refines (While C P) (While C Q).
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply While_monotonic_refines.
Qed.

Theorem refines_extensionality_left : forall T V (P1 P2 Q : @Stmt T V),
    (forall s s', (pred P1) s s' <-> (pred P2) s s') -> refines P1 Q <-> refines P2 Q.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply refines_extensionality_left.
Qed.

Theorem refines_extensionality_right : forall T V (P Q1 Q2 : @Stmt T V),
    (forall s s', (pred Q1) s s' <-> (pred Q2) s s') -> refines P Q1 <-> refines P Q2.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply refines_extensionality_right.
Qed.

Theorem refines_extensionality : forall T V (P1 P2 Q1 Q2 : @Stmt T V),
    (forall s s', (pred P1) s s' <-> (pred P2) s s')
    -> (forall s s', (pred Q1) s s' <-> (pred Q2) s s')
    -> refines P1 Q1 <-> refines P2 Q2.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply refines_extensionality.
Qed.


Theorem wfd_while_iff_if : forall { T : Type } C (P : @Stmt T T),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> forall s s', while C P s s' <-> pred (IIf C Then P End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHrefines s s'.
  rewrite refines_predicative_refines in HHrefines.
  apply ImprovedPredicative.wfd_while_iff_if; auto.
Qed.

Theorem wfd_while_refines_if : forall { T : Type } C (P : @Stmt T T),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply ImprovedPredicative.wfd_while_refines_if.
Qed.

Theorem if_refines_wfd_while : forall { T : Type } C (P : @Stmt T T),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End ⊑ WWhile C Do P Done.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply if_refines_wfd_while.
Qed. 

Theorem wfd_while_iff_if' : forall { T : Type } C (P : @Stmt T T),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> pred P s sx)
               /\ (C s' /\ (exists sx, pred P s' sx) \/ ~ C s'))
    -> forall s s', while C P s s' <-> pred (IIf C Then P End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHrefines s s'.
  apply ImprovedPredicative.wfd_while_iff_if'; auto.
Qed.

Theorem wfd_while_refines_if' : forall { T : Type } C (P : @Stmt T T),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> pred P s sx)
               /\ (C s' /\ (exists sx, pred P s' sx) \/ ~ C s'))
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply ImprovedPredicative.wfd_while_refines_if'.
Qed.

Theorem while_rule_sound_and_complete : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    <-> exists K, P ⊑ K
           /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
           /\ (⟨fun s s' => C s /\ pred K s s'⟩;⟨fun s s' => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred K s s'⟩
           /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros *.
  repeat setoid_rewrite refines_predicative_refines.
  repeat setoid_rewrite refines_old_refines.
  apply ImprovedPredicative.while_rule_sound_and_complete.
Qed.

Lemma wpr_and : forall { T U V } (P : @Stmt U V) (K1 K2 : T >> V) s s',
    wpr P (fun s s' => K1 s s' /\ K2 s s') s s' <-> wpr P K1 s s' /\ wpr P K2 s s'.
Proof.
  setoid_rewrite <- wpr_pred; simpl.
  setoid_rewrite wpr_spec_and.
  reflexivity.
Qed.

Theorem wpr_while_wpr_if : forall  U V (C : @Predicate V) (P : @Stmt V V) (R : U >> V) s s',
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> wpr (WWhile C Do P Done) R s s' <-> wpr (IIf C Then P End) (fun s s' => ~ C s' -> R s s') s s'.
Proof.
  intros.
  apply wpr_while_wpr_if'.
  { clear H0.
    rewrite (Wfd.by_extensionality).
    { apply H. }
    { simpl; repeat setoid_rewrite <- pred_old_pred.
      reflexivity.
    }
  }
  { rewrite <- refines_predicative_refines.
    rewrite <- refines_extensionality.
    { apply H0. }
    { simpl.
      intros.
      apply DemonicComposition.extensionality; setoid_rewrite <- pred_old_pred; reflexivity.
    }
    { simpl. setoid_rewrite <- pred_old_pred; reflexivity. }
  }
Qed.
  
Close Scope stmt_scope.