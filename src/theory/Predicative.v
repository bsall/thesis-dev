Require Import Predicate DemonicComposition DemonicJoin AngelicComposition Specification Statement LeastFixpoint Wfd TransitiveClosure.

Open Scope stmt_scope.

Definition while_functional { T : Type } (C : @Predicate T)(P : T >> T)(X : T >> T) := fun s s' => (C s /\ (P ⊟ X) s s') \/ (~ C s /\ s = s').

Lemma while_functional_monotonic :
  forall { T : Type } (C : @Predicate T) (P X1 X2 : T >> T),
    (forall s s', X1 s s' -> X2 s s') -> (forall s s', while_functional C P X1 s s' -> while_functional C P X2 s s').
Proof.
  intros T C P X1 X2 HHx1x2 s s' [ [HHwhile1 HHwhile2] | HHwhile ]; unfold while_functional.
  { left.
    split; auto.
    apply (right_monotonic _ _ _ _ _ _ HHx1x2 _ _ HHwhile2).
  }
  { right; exact HHwhile. }
Qed.

Definition while { T : Type } (C : @Predicate T) (P : T >> T) := lfp (while_functional C P).

Theorem while_end : forall (T : Type) (C : @Predicate T) (P : T >> T) s s', while C P s s' -> ~ C s'.
Proof.
  intros T C P s s' HHwhile.
  unfold while in HHwhile.
  pattern s,s'.
  eapply (f_lfp _ _ _ _ _ HHwhile).
  Unshelve.
  intros r r' HH. firstorder.
  subst r; exact H.
Qed.

Theorem while_destruct : forall { T : Type } (C : @Predicate T) P s s', while C P s s' -> (C s /\ (P ⊟ (while C P)) s s') \/ (~ C s /\ s = s').
Proof.
  intros.
  apply (lfp_f_lfp _ (while_functional_monotonic C P)) in H; auto.
Qed.

Theorem while_construct : forall { T : Type } (C : @Predicate T) P s s', (C s /\ (P ⊟ (while C P)) s s') \/ (~ C s /\ s = s') -> while C P s s'.
Proof.
  intros.
  apply (f_lfp_lfp _ (while_functional_monotonic C P)) in H; auto.
Qed.

Theorem while_fix : forall { T : Type } (C : @Predicate T) P s s', while C P s s' <-> (C s /\ (P ⊟ (while C P)) s s') \/ (~ C s /\ s = s').
Proof.
  split.
  { apply while_destruct. }
  { apply while_construct. }
Qed.

Theorem while_ind : forall { T : Type } (C : @Predicate T) P X s s',
    while C P s s' -> (forall s s', ((C s /\ (P ⊟ X) s s') \/ (~ C s /\ s = s')) -> X s s') -> X s s'.
Proof.
  intros T C P X s s' HHwhile HH.
  eapply (f_lfp _ _ _ _ _ HHwhile).
  Unshelve.
  auto.
Qed.

Theorem ex_while_ind : forall { T : Type } (C : @Predicate T) P (X : Predicate) s,
    (exists s', while C P s s') -> (forall s, ((C s /\ (forall sx, P s sx -> X sx)) \/ (~ C s)) -> X s) -> X s.
Proof.
  intros T C P X s (s',HHwhile).
  pattern s,s'; apply HHwhile.
  intros.
  unfold while_functional in H.
  apply H0.
  destruct H.
  { destruct H. left; split; auto.
    destruct H1.
    intros.
    destruct (H2 _ H3).
    apply H4.
    auto. 
  }
  { right; firstorder. }
Qed.
  
Theorem while_well_founded : forall { T : Type } (p : @Predicate T) (C : T >> T),
    well_founded (fun s s' => p s' /\ C s' s /\ (exists r, (while p C) s' r)).
Proof.
  intros T p C.
  constructor. 
  intros y [HHp [HHpred HHwhile]].
  generalize y HHp HHpred; clear y HHp HHpred.
  pattern a; apply (ex_while_ind _ _ _ _ HHwhile).
  intros s [ (_,H2) | H ]; try contradiction.
  constructor; intros y' (HHpy,(HHc,_)).
  apply (H2 y); auto.
Qed.

Lemma wfd_prefix_while : forall { T : Type } (C : @Predicate T) (P K : T >> T),
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (forall s s', K s s' -> ((C s /\ (P ⊟ K) s s') \/ (~ C s /\ s = s')))
    -> forall s s', K s s' -> while C P s s'.
Proof.
  intros T C P K HHwfd HHT1 s.
  pattern s; apply (well_founded_ind HHwfd).
  intros sx HH s' HHK.
  pose proof (HHT1 _ _ HHK).
  destruct H as [(HHc,((sy,(HH11,HH12)),HH13)) | HH2].
  { apply while_construct; left; split; auto; split; auto.
    { exists sy; split; auto.
      destruct (HHT1 _ _ HH12).
      { apply HH; auto.
        destruct H; auto.
      }
      { apply while_construct; auto. }
    }
    { intros sz HHp2.
      pose proof (HH13 _ HHp2) as (sz',HHT2).
      exists sz'.
      destruct (HHT1 _ _ HHT2).
      { destruct H; apply HH; auto; split; auto; split; auto; eauto. }
      { apply while_construct; auto. }
    }
  }
  { apply while_construct; right; auto. }
Qed.

Theorem wfd_fix_while : forall { T : Type } (C : @Predicate T) (P K : T >> T),
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (forall s s', K s s' <-> ((C s /\ (P ⊟ K) s s') \/ (~ C s /\ s = s')))
    -> forall s s', K s s' <-> while C P s s'.
Proof.
  intros T C P K HHwfd HHK s s'.
  split.
  { apply wfd_prefix_while; auto.
    apply HHK.
  }
  { intros HHwhile.
    apply (while_ind _ _ _ _ _ HHwhile).
    apply HHK.
  }
Qed.

Theorem while_extensionality :
  forall { T : Type } (C1 : @Predicate T) P1 C2 P2,
    (forall s, C1 s <-> C2 s) -> (forall s s', P1 s s' <-> P2 s s') -> forall s s', while C1 P1 s s' <-> while C2 P2 s s'.
Proof.
  intros T C1 P1 C2 P2 HHequiv1 HHequiv2 s s'.
  unfold while.
  apply lfp_extensionality.
  clear s s'.
  unfold while_functional.
  intros X s s'.
  rewrite HHequiv1.
  rewrite (DemonicComposition.left_extensionality _ _ _ HHequiv2).
  reflexivity.
Qed.

(* Statement to Predicate *)
Fixpoint pred { T V : Type } (C : @Stmt T V) { struct C }
: Specification :=
  match C with
  | Void => fun s s' => False
  | Assignment effect => fun s s' => effect s = s'
  | Seq c1 c2 => (pred c1) ⊟ (pred c2)
  | If p ct cf => fun s s' => (p s /\ pred ct s s') \/ (~ p s /\ pred cf s s')
  | While p c => while p (pred c)
  | Spec spec => spec
  | Guarded p c => fun s s' => (p s /\ pred c s s')
  | Choice c1 c2 => (pred c1) ⊔ (pred c2)
  end.

Opaque while.

Definition refines { T V : Type } (S1 S2 : @Stmt T V) :=
  forall s, (exists s', pred S2 s s') -> (forall s', pred S1 s s' -> pred S2 s s') /\ (exists s', pred S1 s s').

(*
Theorem refines_morphism :
  forall { T : Type } (P Q : T >> T) (f : T -> T),
    (forall s s', P (f s) s' -> exists r', f r' = s')
    -> (forall s s', Q s s' -> Q (f s) (f s'))
    -> (forall s s', (exists s', P s s') -> P (f s) (f s') -> P s s')
    -> (forall s, (exists s', P s s') -> (exists s', P (f s) (f s')))
    -> forall s, ((forall s', P s s' -> Q s s') /\ (exists s', P s s'))
           -> ((forall s', P (f s) s' -> Q (f s) s') /\ (exists s', P (f s) s')).
Proof.
  intros * HHsurj HHsimq HHsimp HHsimp' s (HHpq,HHep).
  split.
  { intros t' HHp.
    destruct (HHsurj _ _ HHp) as (s',HHeq); subst.
    apply HHsimq,HHpq,(HHsimp _ _ HHep HHp).
  }
  { destruct (HHsimp' _ HHep) as (s',HHp).
    exists (f s'); exact HHp.
  }
Qed.
*)
Lemma refines_dom : forall T V (C : @Predicate T) (P : @Stmt T V), refines P (⟨fun s s' => pred P s s' /\ C s⟩).
Proof. firstorder. Qed.

Lemma while_P_while_while : forall T (C : @Predicate T) (P : T >> T) s s',
    while C (fun s s' => P s s' /\ (exists s', while C P s s')) s s' -> while C P s s'.
Proof.
   intros T C P s s' HHwhile.
   pattern s,s'; apply (while_ind _ _ _ _ _ HHwhile).
   clear s s' HHwhile.
   intros.
   destruct H.
   { destruct H.
     destruct H0.
     destruct H0 as (sx,((HHpssx,HHex),HHwhile)).
     apply while_construct; left; split; auto.
     split; eauto.
   }
   { apply while_construct; right; auto. } 
Qed.

Theorem wfd_while_while :
  forall T (C : @Predicate T) P,
  exists Q, well_founded (fun s s' => C s' /\ (pred Q) s' s)
       /\ refines P Q
       /\ forall s s', while C (pred Q) s s' <-> while C (pred P) s s'. 
Proof.
  intros T C P.
  exists (⟨fun s s' => pred P s s' /\ exists s', while C (pred P) s s'⟩).
  split.
  { apply (while_well_founded C (pred P)). }
  { split.
    { apply refines_dom. }
    { split; intros HHwhile.
      { apply (while_P_while_while _ C (pred P) _ _ HHwhile). } 
      { pattern s,s'; apply (while_ind _ _ _ _ _ HHwhile).
        clear s s' HHwhile.
        intros.
        destruct H.
        { destruct H.
          destruct H0.
          apply while_construct; left; split; auto.
          destruct H0 as (sx,(HHp,HHwhile)).
          destruct (H1 _ HHp) as (sx',HHwhile').
          split.
          { exists sx; split; auto.
            split; auto.
            exists s'.
            apply while_construct; left; split; auto.
            split.
            { exists sx; split; auto.
              apply (while_P_while_while _ C (pred P) _ _ HHwhile).
            }
            { intros sy HHpssy.
              destruct (H1 _ HHpssy) as (sy',HHsy').
              exists sy'.
              apply (while_P_while_while _ C (pred P) _ _ HHsy').
            }
          }
          { intros sy (HHpssy,HHex).
            apply H1; auto.
          }
        }
        { apply while_construct; right; auto. }
      }
    }
  }
Qed.

Theorem refines_reflexive : forall (T V : Type)  (P : @Stmt T V), refines P P.
Proof. firstorder. Qed.
  
Theorem refines_trans : forall (T V : Type)  (P Q R : @Stmt T V), refines P Q -> refines Q R -> refines P R.
Proof.
  intros T V P' Q' R'.
  unfold refines.
  generalize (pred P') as P, (pred Q') as Q, (pred R') as R; clear P' Q' R'.
  intros P Q R HHrefpq HHrefqr s HHr.
  split.
  { intros s' HHp.
    apply (HHrefqr _ HHr).
    apply HHrefpq; auto.
    apply (HHrefqr _ HHr).
  }
  { apply HHrefpq.
    apply (HHrefqr _ HHr).
  }
Qed.

Theorem if_extensionality :
  forall { T : Type } (C1 : @Predicate T) P1 C2 P2,
    (forall s, C1 s <-> C2 s) -> (forall s s', P1 s s' <-> P2 s s') -> forall s s', pred (IIf C1 Then ⟨P1⟩ End) s s' <-> pred (IIf C2 Then ⟨P2⟩ End) s s'.

Proof.
  intros T C1 P1 C2 P2 HHequiv1 HHequiv2 s s'.
  simpl. rewrite HHequiv1,HHequiv2. reflexivity.
Qed.

Theorem Seq_left_monotonic_refines :
  forall (T U V : Type) (P1 P2 : @Stmt T U) (Q : @Stmt U V), refines P1 P2 -> refines (Seq P1 Q) (Seq P2 Q).
Proof.
  intros T U V P1 P2 Q HHrefines.
  unfold refines in *.
  intros s (s',((sx,(HHp2,HHq)),HHp2q)).
  split.
  { firstorder. }
  { destruct (HHrefines _ (ex_intro _ _ HHp2)) as (HHp1p2,(sy,HHp1)).
    destruct (HHp2q _ (HHp1p2 _ HHp1)) as (sy',HHq').
    exists sy'; split; eauto.
  }
Qed.

Theorem Seq_right_monotonic_refines :
  forall (T U V : Type) (P : @Stmt T U) (Q1 Q2 : @Stmt U V), refines Q1 Q2 -> refines (Seq P Q1) (Seq P Q2).
Proof.
  intros T U V P Q1 Q2 HHrefines.
  unfold refines in *.
  intros s (s',((sx,(HHp,HHq2)),HHpq2)).
  split.
  { intros s'' ((sy,(HHp',HHq1)),HH2).
    split; auto.
    exists sy; split; auto.
    apply (HHrefines _ (HHpq2 _ HHp')); auto.
  }
  { destruct (HHrefines _ (ex_intro _ _ HHq2)) as (HHq1q2,(sy,HHp')).
    exists sy; split; eauto.
    intros sz HHp''.
    apply (HHrefines _ (HHpq2 _ HHp'')).
  }
Qed.

Theorem Seq_monotonic_refines :
  forall (T U V : Type) (P1 Q1 : @Stmt T U) (P2 Q2 : @Stmt U V),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (Seq P1 P2) (Seq Q1 Q2).
Proof.
  intros T U V P1 Q1 P2 Q2 HHref11 HHref22.
  apply (refines_trans _ _ _ _ _
                       (Seq_right_monotonic_refines _ _ _ P1 P2 Q2 HHref22)
                       (Seq_left_monotonic_refines _ _ _ P1 Q1 Q2 HHref11)).
Qed.

Theorem If_monotonic_refines :
  forall (T V : Type) C (Pt Qt Pf Qf : @Stmt T V),
    refines Pt Qt
    -> refines Pf Qf
    -> refines (If C Pt Pf) (If C Qt Qf).
Proof.
  intros T V C Pt' Pf' Qt' Qf'.
  unfold refines; simpl.
  generalize (pred Pt') as Pt, (pred Pf') as Pf, (pred Qt') as Qt, (pred Qf') as Qf; clear Pt' Pf' Qt' Qf'.
  intros Pt Pf Qt Qf HHref1 HHref2.
  firstorder.
Qed.


Theorem When_monotonic_refines :
  forall (T V : Type) C (P Q : @Stmt T V),
    refines P Q
    -> refines (WWhen C Then P End) (WWhen C Then Q End).
Proof.
  intros T V C P Q.
  unfold refines; simpl.
  generalize (pred P) as P', (pred Q) as Q'; clear P Q.
  intros P Q HHref.
  firstorder.
Qed.

Theorem If_monotonic_refines2 :
  forall (T V : Type) C (Pt Qt Pf Qf : @Stmt T V),
    refines (Guarded C Pt) (Guarded C Qt)
    -> refines (Guarded (fun s => ~ C s) Pf) (Guarded (fun s => ~ C s) Qf)
    -> refines (If C Pt Pf) (If C Qt Qf).
Proof.
  intros T V C Pt' Pf' Qt' Qf'.
  unfold refines; simpl.
  generalize (pred Pt') as Pt, (pred Pf') as Pf, (pred Qt') as Qt, (pred Qf') as Qf; clear Pt' Pf' Qt' Qf'.
  intros Pt Pf Qt Qf HHref1 HHref2.
  firstorder.
Qed.

Theorem Choice_left_monotonic_refines :
  forall (T V : Type) (P1 P2 : @Stmt T V) (Q : @Stmt T V), refines P1 P2 -> refines (P1 ⫾ Q) (P2 ⫾ Q).
Proof. firstorder. Qed.

Theorem Choice_right_monotonic_refines :
  forall (T V : Type) (P : @Stmt T V) (Q1 Q2 : @Stmt T V), refines Q1 Q2 -> refines (P ⫾ Q1) (P ⫾ Q2).
Proof. firstorder. Qed.

Theorem Choice_monotonic_refines :
  forall (T V : Type) (P1 Q1 : @Stmt T V) (P2 Q2 : @Stmt T V),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (P1 ⫾ P2) (Q1 ⫾ Q2).
Proof.
  intros T V P1 Q1 P2 Q2 HHref11 HHref22.
  apply (refines_trans _ _ _ _ _
                       (Choice_right_monotonic_refines _ _ P1 P2 Q2 HHref22)
                       (Choice_left_monotonic_refines _ _ P1 Q1 Q2 HHref11)).
Qed.

Theorem While_monotonic_refines :
  forall (T : Type) C (P Q : @Stmt T T),
    refines P Q
    -> refines (While C P) (While C Q).
Proof.
  intros T C P' Q'.
  unfold refines; simpl.
  generalize (pred P') as P, (pred Q') as Q; clear P' Q'.
  intros P Q HHref.
  intros s (s',HHwhileQ).
  split.
  { intros s'' HHwhileP.
    generalize s' HHwhileQ; clear s' HHwhileQ.
    pattern s,s''; apply (while_ind _ _ _ _ _ HHwhileP); clear s s'' HHwhileP.
    intros s s' [ (HHc,((sy,(HHp,HHq)),HH22)) | (HHc,HHeq) ].
    { intros t HHwhileQ.
      apply while_destruct in HHwhileQ as [ (_,((sx,(HH11,HH12)),HH2)) | (HHc',_)]; try contradiction.
      apply while_construct; left; split; auto.
      split; auto.
      assert (Q s sy) as HHqsy.
      { apply (HHref _ (ex_intro _ _ HH11)); auto. }
      exists sy; split; auto.
      destruct (HH2 _ HHqsy) as (sy',HHwhileQ).
      apply (HHq _ HHwhileQ).
    }
    { subst s.
      intros _ _.
      apply while_construct; right; auto.
    }
  }
  { generalize s' HHwhileQ; clear s' HHwhileQ.
    pattern s; apply (well_founded_ind (while_well_founded C Q)); clear s.
     intros s HHind s' HHwhileQ.
    destruct (while_destruct _ _ _ _ HHwhileQ) as [ (HHc,((sx,(HHq,HHwhileQ')),HH2)) | (HHc,HHeq) ].
    { destruct (HHref _ (ex_intro _ _ HHq)) as (HHpq,(sy,HHpsy)).
      pose proof (HHind _ (conj HHc (conj (HHpq _ HHpsy) (ex_intro _ _ HHwhileQ)))) as HHind'.
      destruct (HH2 _ (HHpq _ HHpsy)) as (sy',HHwhileQ'').
      destruct (HHind' _ HHwhileQ'') as (sy'',HHwhileP).
      exists sy''.
      apply while_construct.
      left; split; auto.
      split; eauto.
      intros sz HHpsz.
      destruct (HH2 _ (HHpq _ HHpsz)) as (sz',HHwhileQz).
      pose proof (HHind _ (conj HHc (conj (HHpq _ HHpsz) (ex_intro _ _ HHwhileQ)))) as HHindz.
      apply (HHindz _ HHwhileQz).
    }
    { exists s'; apply while_construct; right; auto. }
  }
Qed.

Notation "C1 ⊑ C2" := (refines C1 C2) (at level 60, format "C1  ⊑  C2").

Require Import Decidable.
Require Import Lia.


Lemma wfd_while1' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (forall s sx, C s /\ P s sx -> C sx /\ (exists s'', P sx s'') \/ ~ C sx)
    -> forall s s', pred (IIf C Then ⟨P⟩ End) s s' -> ~ C s' -> while C P s s'.
Proof.
  intros T C P HHwfd HHrefines s s' [ (HHCs,HHpred) | HH ] HHcs'.
  { apply while_construct; left; split; auto.
    split.
    { exists s'; split; auto.
      apply while_construct; right; auto.
    }
    { intros sx HHpsx. 
      { clear HHpred HHcs'.
        generalize HHCs sx HHpsx; clear HHCs sx HHpsx.
        pattern s; apply (well_founded_ind HHwfd).
        intros.
        destruct (HHrefines _ _ (conj HHCs HHpsx)) as [(HHcsx,(x0,HHpsx')) | HHncsx]; simpl in *.
        { assert (exists s', while C P x0 s') as H1.
          { apply (H sx); auto. }
          destruct H1 as (sz, HHwhile).
          exists sz.
          apply while_construct; left; split; auto. 
          split; eauto.
        }
        { exists sx; apply while_construct; right; auto. }
      }
    }
  }
  { apply while_construct; right; auto. }
Qed.

Lemma wfd_while1 : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (⟨fun s s' => C s /\ P s s'⟩;⟨fun s s' => C s /\ P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ P s s'⟩
    -> forall s s', pred (IIf C Then ⟨P⟩ End) s s' -> ~ C s' -> while C P s s'.
Proof.
  intros T C P HHwfd HHrefines s s' [ (HHCs,HHpred) | HH ] HHcs'.
  { apply while_construct; left; split; auto.
    split.
    { exists s'; split; auto.
      apply while_construct; right; auto.
    }
    { intros sx HHpsx. 
      { clear HHpred HHcs'.
        generalize HHCs sx HHpsx; clear HHCs sx HHpsx.
        pattern s; apply (well_founded_ind HHwfd).
        intros.
        destruct (HHrefines _ (ex_intro _ _ (conj HHCs HHpsx))); simpl in *.
        destruct H1 as (s'',(HH21,HH22)).
        destruct (HH22 _ (conj HHCs HHpsx)).
        rename H1 into HHpsx'. 
        (* pose proof (H _ (conj HHCs (conj HHpsx H0)) H0) as HH. *)
        assert (exists s', while C P x0 s').
        { destruct HHpsx' as [ (HHCsx,HHpsx') | (HHncsx,HHeq) ].
          { pose proof (H _ (conj HHCs (conj HHpsx HHCsx)) HHCsx _ HHpsx').
            auto.
          }
          { subst x0; exists sx; apply while_construct; right; auto. }
        }
        destruct H1 as (sz, HHwhile).
        destruct HHpsx' as [ (HHCsx,HHpsx') | (HHncsx,HHeq) ]; auto.
        { exists sz.
          apply while_construct; left; split; auto. 
          split; eauto.
        }
        { exists sz; subst x0. auto. }
      }
    }
  }
  { apply while_construct; right; auto. }
Qed.

Lemma wfd_while2 : forall { T : Type } (C : @Predicate T) P,
    (⟨fun s s' => C s /\ P s s'⟩;⟨fun s s' => C s /\ P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ P s s'⟩
    -> forall s s', while C P s s' -> pred (IIf C Then ⟨P⟩ End) s s' /\ ~ C s'.
Proof.
  intros T C P HHrefines s s' HHwhile.
  pattern s,s'; apply (while_ind _ _ _ _ _ HHwhile).
  clear s s' HHwhile.
  intros s s' [ (HHc,((sx,(HHpssx,(HHif,HHcs'))),HHtrm)) | (HHc,HHeq)].
  { simpl.
    destruct HHif as [HHif | HHif].
    { split; auto.
      left; apply HHrefines; simpl.
      { eauto. }
      { split.
        { firstorder. }
        { intros sy (HHcsy,HHpssy).
          destruct (HHtrm _ HHpssy) as (sy',(HHif_sy,HHcsy')).
          simpl in HHif_sy. eauto. 
        }
      }
    }
    { simpl in *.
      split; auto.
      destruct HHif as (_,HHeq); subst sx.
      left; auto.
    }
  }
  { subst s'.
    firstorder.
  }
Qed.

Lemma wfd_while2' : forall { T : Type } (C : @Predicate T) P,
    (forall s sx, C s /\ P s sx -> forall s', (C sx /\ P sx s' \/ ~ C sx /\ sx = s') -> P s s')
    -> forall s s', while C P s s' -> pred (IIf C Then ⟨P⟩ End) s s' /\ ~ C s'.
Proof.
  intros T C P HHrefines s s' HHwhile.
  pattern s,s'; apply (while_ind _ _ _ _ _ HHwhile).
  clear s s' HHwhile.
  intros s s' [ (HHc,((sx,(HHpssx,(HHif,HHcs'))),HHtrm)) | (HHc,HHeq)].
  { simpl.
    destruct HHif as [HHif | HHif].
    { split; auto.
      left; split; auto; apply (HHrefines _ sx); auto.
    }
    { simpl in *.
      split; auto.
      destruct HHif as (_,HHeq); subst sx.
      left; auto.
    }
  }
  { subst s'.
    firstorder.
  }
Qed.

Lemma wfd_while2'' : forall { T : Type } (C : @Predicate T) P,
    (forall s sx, C s /\ P s sx -> forall s', (C sx /\ P sx s' /\ ~ C s') -> P s s')
    -> forall s s', while C P s s' -> pred (IIf C Then ⟨P⟩ End) s s' /\ ~ C s'.
Proof.
  intros T C P HHrefines s s' HHwhile.
  pattern s,s'; apply (while_ind _ _ _ _ _ HHwhile).
  clear s s' HHwhile.
  intros s s' [ (HHc,((sx,(HHpssx,(HHif,HHcs'))),HHtrm)) | (HHc,HHeq)].
  { simpl.
    destruct HHif as [HHif | HHif].
    { split; auto.
      left; split; auto; apply (HHrefines _ sx); auto.
      destruct HHif; auto.
    }
    { simpl in *.
      split; auto.
      destruct HHif as (_,HHeq); subst sx.
      left; auto.
    }
  }
  { subst s'.
    firstorder.
  }
Qed.

Lemma wfd_while_iff_if : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (⟨fun s s' => C s /\ P s s'⟩;⟨fun s s' => C s /\ P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ P s s'⟩
    -> forall s s', while C P s s' <-> pred (IIf C Then ⟨P⟩ End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHrefines s s'.
  split.
  { apply (wfd_while2 _ _ HHrefines). }
  { intros (HHpred,HHc).
    apply (wfd_while1 _ _ HHwfd HHrefines _ _ HHpred HHc).
  }
Qed.

Lemma wfd_while_iff_if'' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (forall s s', C s /\ P s s' -> C s' /\ (exists sx, P s' sx) \/ ~ C s')
    -> (forall s s', C s /\ P s s' -> forall sx, (C s' /\ P s' sx /\ ~ C sx) -> P s sx)
    -> forall s s', while C P s s' <-> pred (IIf C Then ⟨P⟩ End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHsnd1 HHsnd2 s s'.
  split.
  { apply (wfd_while2'' _ _ HHsnd2). }
  { intros (HHpred,HHc).
    apply (wfd_while1' _ _ HHwfd HHsnd1 _ _ HHpred HHc).
  }
Qed.

Lemma wfd_while_iff_if' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ P s' s /\ C s)
    -> (forall s s', C s /\ P s s' -> C s' /\ (exists sx,P s' sx) \/ ~ C s')
    -> (forall s s', C s /\ P s s' -> forall sx, (C s' /\ P s' sx \/ ~ C s' /\ s' = sx) -> P s sx)
    -> forall s s', while C P s s' <-> pred (IIf C Then ⟨P⟩ End) s s' /\ ~ C s'.
Proof.
  intros T C P HHwfd HHsnd1 HHsnd2 s s'.
  split.
  { apply (wfd_while2' _ _ HHsnd2). }
  { intros (HHpred,HHc).
    apply (wfd_while1' _ _ HHwfd HHsnd1 _ _ HHpred HHc).
  }
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
    firstorder.
  }
  { exists s''.
    rewrite (wfd_while_iff_if _ _ HHwfd HHrefines).
    simpl.
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
    intros [HHpred | HHskip].
    { firstorder. }
    { destruct HHskip; subst s'.
      firstorder.
    }
  }
  { exists s''.
    rewrite (wfd_while_iff_if _ _ HHwfd HHrefines) in HHtrm.
    simpl in HHtrm.
    destruct HHtrm as ([ HHtrm | (HHc,HHeq) ], HHc').
    { firstorder. }
    { subst s''; firstorder. }
  }
Qed.

Theorem wfd_while_refines_if'' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx /\ ~ C sx) -> pred P s sx)
               /\ (C s' /\ (exists sx, pred P s' sx) \/ ~ C s'))
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros * HHwfd HHsnd.
  unfold refines; simpl.
  intros * (s'',HHtrm).
  split.
  { intros s'.
    rewrite (wfd_while_iff_if'' _ _ HHwfd).
    { simpl. firstorder. }
    all : apply HHsnd.
  }
  { exists s''.
    rewrite (wfd_while_iff_if'' _ _ HHwfd).
    { simpl.
      destruct HHtrm.
      { firstorder. }
      { destruct H; subst s''; firstorder. }
    }
    all : apply HHsnd.
  }
Qed.

Theorem wfd_while_refines_if' : forall { T : Type } (C : @Predicate T) P,
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> pred P s sx)
               /\ (C s' /\ (exists sx, pred P s' sx) \/ ~ C s'))
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros * HHwfd HHsnd.
  unfold refines; simpl.
  intros * (s'',HHtrm).
  split.
  { intros s'.
    rewrite (wfd_while_iff_if' _ _ HHwfd).
    { simpl. firstorder. }
    all : apply HHsnd.
  }
  { exists s''.
    rewrite (wfd_while_iff_if' _ _ HHwfd).
    { simpl.
      destruct HHtrm.
      { firstorder. }
      { destruct H; subst s''; firstorder. }
    }
    all : apply HHsnd.
  }
Qed.

Lemma while_rule_sound'' : forall { T : Type } (C : @Predicate T) P K R,
    P ⊑ K 
    -> well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
    -> (forall s s', C s /\ pred K s s' ->
               (forall sx, (C s' /\ pred K s' sx /\ ~ C sx) -> pred K s sx)
               /\ (C s' /\ (exists sx, pred K s' sx) \/ ~ C s'))
    -> IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R
    -> WWhile C Do P Done ⊑ R.
Proof.
  intros.
  eapply (refines_trans _ _ _ _ _ _ H2).
  Unshelve.
  apply (refines_trans _ _ _ (WWhile C Do K Done)).
  { apply (While_monotonic_refines _ _ _ _ H). }
  { apply (wfd_while_refines_if'' _ _ H0 H1). }
Qed.

Lemma while_rule_sound : forall { T : Type } (C : @Predicate T) P K R,
    P ⊑ K 
    -> well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred K s s'⟩;⟨fun s s' => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred K s s'⟩
    -> IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R
    -> WWhile C Do P Done ⊑ R.
Proof.
  intros.
  eapply (refines_trans _ _ _ _ _ _ H2).
  Unshelve.
  apply (refines_trans _ _ _ (WWhile C Do K Done)).
  { apply (While_monotonic_refines _ _ _ _ H). }
  { apply (wfd_while_refines_if _ _ H0 H1). }
Qed.

Theorem refines_tcl : forall T (R : T -> T -> Prop), ⟨R⟩ ⊑ ⟨tcl R⟩.
Proof.
  intros *.
  unfold refines; simpl.
  intros.
  split.
  { setoid_rewrite tcl_fix; auto. }
  { apply tcl_dom; auto. }
Qed.

Definition kernel { T } (R : T -> T -> Prop) := fun i i' => R i i' /\ (forall j, ~ (R i j /\ R j i')).

Definition deterministic { T } (R : T -> T -> Prop) := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Lemma ll1 : deterministic (kernel (fun i i' => i < i')).
Proof.
  intros i i' i''; unfold kernel; intros; simpl in *.
  destruct H,H0.
  pose proof (H1 i'').
  pose proof (H2 i').
  lia.
Qed.


Lemma while_rule_complete'' : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    -> let K := ⟨tcl (fun s s' => C s /\ pred P s s' /\ exists s', pred (WWhile C Do P Done) s s')⟩ in
      P ⊑ K
      /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
      /\ (forall s s', C s /\ pred K s s' ->
                  (forall sx, (C s' /\ pred K s' sx /\ ~ C sx) -> pred K s sx)
                  /\ (C s' /\ (exists sx, pred K s' sx) \/ ~ C s'))
      /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros.
  (* exists  ⟨tcl (fun s s' => C s /\ pred P s s' /\ exists s', pred (WWhile C Do P Done) s s')⟩; simpl. *)
  split.
  { apply (refines_trans _ _ _  ⟨fun s s' : T => C s /\ pred P s s' /\ (exists s'0 : T, while C (pred P) s s'0)⟩).
    {
      firstorder.
    }
    { apply refines_tcl. }
  }
  { split.
    { apply (Wfd.by_inclusion _ _ (tcl (fun s'0 s0 : T => C s0 /\ pred P s0 s'0 /\ (exists s'1 : T, while C (pred P) s0 s'1)))).
      { rewrite <- tcl_wfd.
        apply while_well_founded.
      }
      { intros x y (_,(HH,_)).
        apply tcl_inv.
        auto.
      }
    }
    { split.
      { simpl.
        intros.
        split.
        { intros.
          destruct H0.
          destruct H1; clear H1. destruct H3; clear H3.
          apply tcl_trans.
          exists s'; auto.
        }
        { intros.
          destruct H0 as (_,HHtcl).
          pattern s in HHtcl.
          pose proof (ex_intro _ _ HHtcl).
          rewrite <- tcl_ran in H0.
          destruct H0 as (r,(HHcr,(HHpr,(r',HHwhiler)))).
          apply while_fix in HHwhiler.
          destruct HHwhiler as [ (_,(_,HHfa)) | (HHcr',_) ]; try contradiction.
          destruct (HHfa _ HHpr) as (sx',HHwhilesx).
          apply while_fix in HHwhilesx.
          destruct HHwhilesx as [ (HHcsx,HH) | (HHdone,_) ]; auto.
          destruct HH as ((sy,(HH111,HH112)),HH12).
          left; split; auto; exists sy; auto.
          apply tcl_fix; right; split; auto.
        }
      }          
      { apply (refines_trans _ _ _ (WWhile C Do P Done)); auto.
        unfold refines; simpl; intros.
        split.
        { intros.
          destruct H1.
          { destruct H1 as (_,H1).
            generalize H0 H1; clear H0 H1.
            pattern s; apply (well_founded_ind (while_well_founded C (pred P))).
            intros.
            apply while_fix; left.
            destruct H2 as (HHtcl,HHnc).
            apply tcl_fix in HHtcl.            
            destruct HHtcl.
            { apply tcl_rotate in H2.
              destruct H2 as (sx,(HH1,HH2)).
              split.
              { clear -HH1; firstorder. }
              { pose proof (ex_intro _ _ HH2) as HHdom.
                apply tcl_dom in HHdom.
                destruct HHdom as (_,(_,(_,HHwsx))).
                pose proof (H0 _ HH1 HHwsx (conj HH2 HHnc)).
                split.
                { exists sx; split; auto. clear -HH1; firstorder. }
                { intros sy HHpsy.
                  destruct H1 as (x',HHwhile).
                  apply while_fix in HHwhile.
                  destruct HHwhile as [ (_,(_,HHfa)) | (HHncx,_)].
                  { apply (HHfa _ HHpsy). }
                  { destruct HH1 as (HHcx,_); contradiction. }
                }
              }
            }
            { split.
              { clear -H2; firstorder. }
              { split.
                { exists s'; split.
                  { clear -H2; firstorder. }
                  { apply while_fix; right; auto. }
                }
                { intros sx HHpsx.
                  destruct H2 as (HHcx,(_,(x',HHw))).
                  apply while_fix in HHw.
                  destruct HHw as [ (_,(_,HHfa)) | (HHncx,_) ].
                  { apply (HHfa _ HHpsx). }
                  { contradiction. }
                }
              }
            }
          }
          { apply while_fix; right; auto. }
        }
        { generalize H0; clear H0.
          pattern s; apply (well_founded_ind (while_well_founded C (pred P))).
          intros.
          destruct H1 as (s',HHwhile).
          pose proof HHwhile as HHwhile'.
          apply while_fix in HHwhile.
          destruct HHwhile as [ (HHc,((sx,(HH1,HH2)),HH3)) | HHdone ].
          { destruct (H0 _ (conj HHc (conj HH1 (ex_intro _ _ HHwhile'))) (ex_intro _ _ HH2)).
            destruct H1.
            { destruct H1 as (HH11,(HH12,HH13)).
              exists x0; left.
              split; auto.
              split; auto.
              apply tcl_fix; left.
              apply tcl_rotate. exists sx.
              firstorder.
            }
            { destruct H1; subst x0; exists sx; left; split; auto.
              split; auto.
              apply tcl_fix; right.
              firstorder.
            }
          }
          { exists x; right; firstorder. }
        }
      }
    }
  }
Qed.

Lemma while_rule_complete : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    -> let K := ⟨tcl (fun s s' => C s /\ pred P s s' /\ exists s', pred (WWhile C Do P Done) s s')⟩ in
      P ⊑ K
      /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
      /\ (⟨fun s s' => C s /\ pred K s s'⟩;⟨fun s s' => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred K s s'⟩
      /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros.
  (* exists  ⟨tcl (fun s s' => C s /\ pred P s s' /\ exists s', pred (WWhile C Do P Done) s s')⟩; simpl. *)
  split.
  { apply (refines_trans _ _ _  ⟨fun s s' : T => C s /\ pred P s s' /\ (exists s'0 : T, while C (pred P) s s'0)⟩).
    {
      firstorder.
    }
    { apply refines_tcl. }
  }
  { split.
    { apply (Wfd.by_inclusion _ _ (tcl (fun s'0 s0 : T => C s0 /\ pred P s0 s'0 /\ (exists s'1 : T, while C (pred P) s0 s'1)))).
      { rewrite <- tcl_wfd.
        apply while_well_founded.
      }
      { intros x y (_,(HH,_)).
        apply tcl_inv.
        auto.
      }
    }
    { split.
      { unfold refines; simpl.
        intros.
        split.
        { intros.
          destruct H1.
          clear H2; destruct H1 as (sx,((HHc,H11),H12)).
          destruct H12 as [(_,H121) | (_,HHeq) ].
          { split; auto.
            apply tcl_trans.
            exists sx; auto.
          }
          { subst sx; split; auto. }
        }
        { destruct H0 as (s',(_,HHtcl)).
          pose proof (ex_intro _ _ HHtcl).
          rewrite <- tcl_dom in H0.
          clear HHtcl s'.

          destruct H0 as (k,(HHc,(HHp,(s',HHwhile)))).
          apply while_fix in HHwhile.
          destruct HHwhile as [ (_,(HH1,HH2)) | (HHc',_) ]; try contradiction.
          destruct (HH2 _ HHp) as (s'',HHwhile).
          exists s'; split.
          { assert (while C (pred P) s s').
            { apply while_fix; left; split; auto.
              split; eauto.
            }
            exists s'.
            split.
            { split; auto.
              destruct HH1 as (sx,(HH11,HH12)).
              generalize s HHc (ex_intro _ _ H0) HH11; clear HHc H0 HH11; pattern sx,s'; apply (while_ind _ _ _ _ _ HH12).
              intros rx r' HH r HHcr H0 HH11.
              destruct HH as [ (HHcrx,((sy,(HH311,HH312)),HH32)) | (HHcr',HHeq) ].
              { apply tcl_fix; left; apply tcl_rotate.
                exists rx; split; eauto.
                apply HH312; auto.
                destruct H0 as (t,HHwhl).
                apply while_fix in HHwhl.
                destruct HHwhl as [ (_,(_,HH)) | (HHncr,_) ]; try contradiction.
                auto.
              }
              { subst rx.
                apply tcl_fix; right; eauto.
              }                              
            }
            { right; split; auto.
              destruct HH1 as (sx,(_,HHw)).
              apply (while_end _ _ _ _ _ HHw).
            }
          }
          { intros.
            destruct H0 as (_,HHtcl).
            pattern s in HHtcl.
            pose proof (ex_intro _ _ HHtcl).
            rewrite <- tcl_ran in H0.
            destruct H0 as (r,(HHcr,(HHpr,(r',HHwhiler)))).
            apply while_fix in HHwhiler.
            destruct HHwhiler as [ (_,(_,HHfa)) | (HHcr',_) ]; try contradiction.
            destruct (HHfa _ HHpr) as (sx',HHwhilesx).
            apply while_fix in HHwhilesx.
            destruct HHwhilesx as [ (HHcsx,HH) | HHdone ]; eauto.
            destruct HH as ((sy,(HH111,HH112)),HH12).
            exists sy; left; split; auto.
            apply tcl_fix; right; split; auto.
          }
        }
      }          
      { apply (refines_trans _ _ _ (WWhile C Do P Done)); auto.
        unfold refines; simpl; intros.
        split.
        { intros.
          destruct H1.
          { destruct H1 as (_,H1).
            generalize H0 H1; clear H0 H1.
            pattern s; apply (well_founded_ind (while_well_founded C (pred P))).
            intros.
            apply while_fix; left.
            destruct H2 as (HHtcl,HHnc).
            apply tcl_fix in HHtcl.            
            destruct HHtcl.
            { apply tcl_rotate in H2.
              destruct H2 as (sx,(HH1,HH2)).
              split.
              { clear -HH1; firstorder. }
              { pose proof (ex_intro _ _ HH2) as HHdom.
                apply tcl_dom in HHdom.
                destruct HHdom as (_,(_,(_,HHwsx))).
                pose proof (H0 _ HH1 HHwsx (conj HH2 HHnc)).
                split.
                { exists sx; split; auto. clear -HH1; firstorder. }
                { intros sy HHpsy.
                  destruct H1 as (x',HHwhile).
                  apply while_fix in HHwhile.
                  destruct HHwhile as [ (_,(_,HHfa)) | (HHncx,_)].
                  { apply (HHfa _ HHpsy). }
                  { destruct HH1 as (HHcx,_); contradiction. }
                }
              }
            }
            { split.
              { clear -H2; firstorder. }
              { split.
                { exists s'; split.
                  { clear -H2; firstorder. }
                  { apply while_fix; right; auto. }
                }
                { intros sx HHpsx.
                  destruct H2 as (HHcx,(_,(x',HHw))).
                  apply while_fix in HHw.
                  destruct HHw as [ (_,(_,HHfa)) | (HHncx,_) ].
                  { apply (HHfa _ HHpsx). }
                  { contradiction. }
                }
              }
            }
          }
          { apply while_fix; right; auto. }
        }
        { generalize H0; clear H0.
          pattern s; apply (well_founded_ind (while_well_founded C (pred P))).
          intros.
          destruct H1 as (s',HHwhile).
          pose proof HHwhile as HHwhile'.
          apply while_fix in HHwhile.
          destruct HHwhile as [ (HHc,((sx,(HH1,HH2)),HH3)) | HHdone ].
          { destruct (H0 _ (conj HHc (conj HH1 (ex_intro _ _ HHwhile'))) (ex_intro _ _ HH2)).
            destruct H1.
            { destruct H1 as (HH11,(HH12,HH13)).
              exists x0; left.
              split; auto.
              split; auto.
              apply tcl_fix; left.
              apply tcl_rotate. exists sx.
              firstorder.
            }
            { destruct H1; subst x0; exists sx; left; split; auto.
              split; auto.
              apply tcl_fix; right.
              firstorder.
            }
          }
          { exists x; right; firstorder. }
        }
      }
    }
  }
Qed.

Theorem while_rule_sound_and_complete'' : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    <-> exists K, P ⊑ K
           /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
           /\ (forall s s', C s /\ pred K s s' ->
                       (forall sx, (C s' /\ pred K s' sx /\ ~ C sx) -> pred K s sx)
                       /\ (C s' /\ (exists sx, pred K s' sx) \/ ~ C s'))
           /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros *.
  split.
  { intros HHwhile.
    apply while_rule_complete'' in HHwhile.
    apply (ex_intro _ ⟨ tcl _⟩ HHwhile).
  }
  { intros (K,(HHk1,(HHk2,(HHk3,HHk4)))).
    apply (while_rule_sound'' _ _ K _ HHk1 HHk2 HHk3 HHk4).
  }
Qed.

Theorem while_rule_sound_and_complete : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    <-> exists K, P ⊑ K
           /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
           /\ (⟨fun s s' => C s /\ pred K s s'⟩;⟨fun s s' => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred K s s'⟩
           /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros *.
  split.
  { intros HHwhile.
    apply while_rule_complete in HHwhile.
    apply (ex_intro _ ⟨ tcl _⟩ HHwhile).
  }
  { intros (K,(HHk1,(HHk2,(HHk3,HHk4)))).
    apply (while_rule_sound _ _ K _ HHk1 HHk2 HHk3 HHk4).
  }
Qed.

Lemma loop_body_refines_equiv : forall T (C : @Predicate T) (K : Stmt T),
  ⟨fun s s' : T => C s /\ pred K s s'⟩;⟨fun s s' : T => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩ ⊑ ⟨fun s s' : T => C s /\ pred K s s'⟩
  <-> (IIf C Then K End);(IIf C Then K End) ⊑ IIf C Then K End.
Proof.
  intros.
  unfold refines; simpl in *.
  split; intros.
  { split; intros.
    { destruct H0 as (s'',[H01|H02]).
      { left; apply H; eauto.
        destruct H1.
        split; auto.
        clear - H01 H0; firstorder.
      }
      { destruct H02; destruct H1.
        subst s.
        destruct H1 as (sx,(H11,H12)).
        destruct H11.
        { destruct H1; contradiction. }
        { destruct H1; subst sx.
          auto.
        }
      }
    }
    { destruct H0 as (s',[H01|(H01,H02)]).
      { destruct (H _ (ex_intro _ _ H01)).
        destruct H1 as (s'',(H1,H2)).
        exists s''; split.
        { clear -H1; firstorder. }
        { intros.
          destruct H3; auto.
          destruct H3; subst sx.
          eauto.
        }
      }
      subst s'.
      exists s; split.
      { exists s; split; auto. }
      { intros.
        exists sx; right.
        destruct H0.
        { destruct H0; contradiction. }
        { destruct H0; subst.
          split; auto.
        }
      }
    }
  }
  { destruct (H s).
    { destruct H0. exists x; auto. }
    { split.
      { intros.
        destruct (H1 s'); auto.
        { destruct H3; split.
          { clear -H3; firstorder. }
          { clear -H0 H4; firstorder. }
        }
        { clear - H0 H4; firstorder. }
      }
      { destruct H2 as (s',(H21,H22)).
        exists s'; split; auto.
        clear - H0 H21; firstorder.
      }
    }
  }
Qed.


Theorem while_rule_sound_and_complete_x : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    <-> exists K, P ⊑ K
           /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
           /\ (let L := IIf C Then K End in L;L ⊑ L)
           /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros.
  rewrite while_rule_sound_and_complete.
  setoid_rewrite loop_body_refines_equiv.
  reflexivity.
Qed.

Theorem refinement_iff : forall T V (S1 S2 : @Stmt T V), (forall s s', pred S1 s s' <-> pred S2 s s') <-> S1 ⊑ S2 /\ S2 ⊑ S1.
Proof.
  intros; split.
  { firstorder. }
  { firstorder.
    { apply H; auto.
      apply H0; eauto.
    }
    { apply H0; auto.
      apply H; eauto.
    }
  }
Qed.  

Close Scope stmt_scope.

