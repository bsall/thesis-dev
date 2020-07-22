Require Import Specification Predicate Statement HoareWp Predicative.

Lemma pred_if_hoare :
  forall (T V : Type) (C : @Stmt T V) P Q, ValidHoareTriple P C Q -> ValidHoareTriple P ⟨pred C⟩ Q.
Proof.
  intros *.
  induction 1.
  { constructor; simpl in *; firstorder. }
  { constructor; simpl in *; firstorder; subst; eauto. }
  { constructor.
    pose proof (spec_inj IHValidHoareTriple1).
    pose proof (spec_inj IHValidHoareTriple2).
    clear -H1 H2.
    intros; split.
    { firstorder. }
    { destruct (H1 _ H).
      destruct H3 as (sx,H3).
      destruct (H2 _ (H0 _ H3)).
      destruct H5 as (s',H5).
      exists s'; split; eauto.
      firstorder.
    }
  }
  { constructor.
    intros; simpl in *.
    pose proof (spec_inj IHValidHoareTriple1).
    pose proof (spec_inj IHValidHoareTriple2).
    clear -H H2 H3 H4.
    split.
    { firstorder. }
    { simpl in *.
      destruct (H _ H2).
      { destruct (H3 _ (conj H0 H2)) as (_,(s',H5)).
        clear - H0 H5; eauto.
      }
      { destruct (H4 _ (conj H0 H2)) as (_,(s',H5)).
        clear - H0 H5; eauto.
      }
    }
  }
  { simpl in *.
    constructor.
    intros s HHPs.
    generalize (H1 _ HHPs).
    pose proof (fun v : W => spec_inj (H3 v)).
    simpl in *.
    clear - H H0 H1 H2 H3 H4 H5.
    pattern s.
    pose proof (Wfd.by_direct_functional_simulation _ _ V _ H0).
    apply (well_founded_ind H6).
    clear - H H1 H4 H5.
    intros s HHind HHI.
    split. 
    { intros.
      apply while_destruct in H0.
      destruct H0 as [ (HHCs,((sx,(H11,H12)),H3)) | (HHnc,HHeq) ]; subst.
      { destruct (H5 _ _ (conj HHCs (conj HHI eq_refl))).
        destruct (H0 _ H11).
        destruct (HHind _ H7 H6).
        exact (H8 _ H12).
      }
      { exact (H4 _ HHnc HHI). }
    }
    { destruct (H _ HHI).
      {  destruct (H5 _ _ (conj H0 (conj HHI eq_refl))).
         destruct H3 as (sx,HHBssx).
         destruct (H2 _ HHBssx).
         destruct (HHind _ H6 H3).
         destruct H8 as (s',HHwhile).
         exists s'.
         apply while_construct; left; split; auto.
         split; eauto.
         clear -H2 HHind.
         firstorder.
      }
      { exists s; apply while_construct; right; auto. }
    }
  }
  { simpl in *.
    constructor; auto.
  }
  { simpl.
    constructor.
    pose proof (spec_inj IHValidHoareTriple).
    firstorder.
  }
  { simpl.
    constructor.
    pose proof (spec_inj IHValidHoareTriple1).
    pose proof (spec_inj IHValidHoareTriple2).
    clear - H1 H2.
    firstorder.
  }
Qed.


Lemma hoare_if_pred :
  forall (T V : Type) (C : @Stmt T V) P Q, ValidHoareTriple P (Statement.Spec (pred C)) Q -> ValidHoareTriple P C Q.
Proof.
  induction C as [ | | | | | | | ]; intros P Q; simpl.
  { intros HHtriple. pose proof (spec_inj HHtriple). clear HHtriple; simpl in *.
    constructor.
    intros.
    unfold not; intros.
    destruct (H _ H0).
    clear - H2; destruct H2.
    auto.
  }
  { intros HHtriple. pose proof (spec_inj HHtriple). clear HHtriple; simpl in *.
    constructor.
    firstorder.
  }
  { intros HHtriple. pose proof (spec_inj HHtriple). clear HHtriple; simpl in *.
    apply (Seq _ _ (fun s => (forall sx, (pred C2) s sx -> Q sx) /\ (exists sx, (pred C2) s sx))).
    { apply (IHC1 _ _); auto; constructor; firstorder. }
    { apply (IHC2 _ _); auto; constructor; firstorder. }
  }
  { intros HHtriple. pose proof (spec_inj HHtriple). clear HHtriple; simpl in *.
    constructor.
    { intros.
      destruct (H _ H0) as (_,(s',[(HHp,_) | (HHn,_) ])).
      { left; auto. }
      { right; auto. }
    }
    { apply (IHC1 _ _); auto; constructor; intros s (HHp1,HHp2); split; firstorder. }
    { apply (IHC2 _ _); auto; constructor; intros s (HHp1,HHp2); split; firstorder. }
  }
  { intros HHtriple. pose proof (spec_inj HHtriple). clear HHtriple; simpl in *.
    apply (While _ _ _ (fun s => (forall s', while p (pred C) s s' -> Q s') /\ exists s', while p (pred C) s s')
                 _ _ (fun s s' => p s' /\ pred C s' s /\ (exists r, (while p (pred C)) s' r))  (fun s => s)).
    { intros.
      destruct H0 as (_,(s',HHwhile)).
      apply while_destruct in HHwhile.
      destruct HHwhile as [ (HHp,_) | (HHn,_)]; unfold Decidable.decidable; auto.
    }
    { constructor. 
      intros y [HHp [HHpred HHwhile]].
      generalize y HHp HHpred; clear y HHp HHpred.
      pattern a; apply (ex_while_ind _ _ _ _ HHwhile).
      intros.
      destruct H0; try contradiction.
      destruct H0.
      constructor; intros.
      destruct H2.
      destruct H3.
      apply (H1 y); auto.
    }
    { auto. }
    { intros.
      apply (IHC _ _); auto.
      constructor.
      intros.
      destruct H0 as (HH1,((HH2,(s',HH3)),HH)); subst v.
      apply while_destruct in HH3.
      destruct HH3 as [ (HH4,((sx,(HH51,HH52)),HH6)) | (HH4,HH5) ]; try contradiction. 
      split; intros.
      { split; intros. 
        { split; intros.
          { apply HH2.
            apply while_construct; left; split; auto.
            split.
            { exists s'0; firstorder. }
            { auto. }
          }
          { apply (HH6 _ H0). }
        }
        { split; auto.
          destruct (HH6 _ H0) as (s'',HH).
          split; auto.
          exists s''; apply while_construct; left; split; auto.
          split; eauto.
        }
      }
      { exists sx; auto. }
    }
    { intros.
      apply H1.
      apply while_construct; right; auto.
    }
  }
  { auto. }
  { intros.
    pose proof (spec_inj H).
    constructor.
    { firstorder. }
    { apply IHC.
      constructor.
      intros.
      firstorder.
    }
  }
  { intros.
    pose proof (spec_inj H).
    constructor.
    { apply IHC1.
      constructor.
      intros.
      firstorder.
      apply (H0 _ H1).
      firstorder.
    }
    { apply IHC2.
      constructor.
      intros.
      firstorder.
      apply (H0 _ H1).
      firstorder.
    }
  }
Qed.

Lemma hoare_pred :
  forall (T V : Type) (C : @Stmt T V) P Q, ValidHoareTriple P C Q <-> ValidHoareTriple P (Statement.Spec (pred C)) Q.
Proof.
  intros T V C P Q.
  split.
  { apply pred_if_hoare; auto. }
  { apply hoare_if_pred; auto. }
Qed.

Theorem hoare_rule_abort : forall T U (P : @Predicate T)(Q : @Predicate U), (forall s, ~ P s) -> P {: abort :} Q.
Proof. intros; constructor; firstorder. Qed.

Theorem hoare_rule_skip : forall T (P : @Predicate T), P {: Skip :} P.
Proof. intros; constructor; auto. Qed.

Theorem hoare_rule_of_consequence : forall T V (P P' : @Predicate T) (Q Q' : @Predicate V) (S : @Stmt T V),
    (forall s, P s -> P' s) -> P' {: S :} Q' -> (forall s, Q' s -> Q s) -> P {: S :} Q.
Proof.
  (* intros.
  induction H0.
  admit.
  admit.
  pose proof (IHValidHoareTriple1 _ Q0 H).
  pose proof (IHValidHoareTriple2 Q0).
  apply (Seq _ _ Q0).
  auto.
  auto.
  constructor.
  auto.
  apply IHValidHoareTriple1; auto.
  firstorder.
  apply IHValidHoareTriple2; auto.
  firstorder.
  Print ValidHoareTriple.
  apply (While _ _ Q I _ _ R V); auto. *)
 (* induction S.
  admit.
  admit.
  intros.
  inversion H0; subst; clear H0.
  inversion_sigma; simpl in *.
  rewrite H2 in *. *)
  intros.
  rewrite hoare_pred.
  rewrite hoare_pred in H0.
  pose proof (spec_inj H0).
  clear H0.
  constructor.
  firstorder.
Qed.

Lemma pred_refines_iff_hoare_refines : forall T V (Q R : T >> V),
    Predicative.refines (Statement.Spec Q) (Statement.Spec R) <-> HoareWp.refines (Statement.Spec Q) (Statement.Spec R).
Proof.
  unfold Predicative.refines, HoareWp.refines; intros; split; intros HHrefines; simpl in *.
  { intros K K' HHr.
    pose proof (spec_inj HHr).
    constructor.
    split; intros.
    { apply (H _ H0).
      apply HHrefines; auto.
      apply (H _ H0).
    }
    { apply HHrefines.
      apply (H _ H0).
    }
  }
  { intros.
    assert (ValidHoareTriple (fun r => r = s) (Statement.Spec R) (fun r' => R s r')).
    { constructor.
      intros r HHr.
      subst r.
      auto.
    }
    apply HHrefines in H0.
    pose proof (spec_inj H0).
    apply (H1 s (eq_refl s)).
  }
Qed.

Theorem hoare_refines_iff_pred_refines_simplified :
  forall T V (Q R : @Stmt T V), HoareWp.refines Q R <-> Predicative.refines Q R.
Proof.
  intros T V Q R.
  unfold HoareWp.refines.
  setoid_rewrite (hoare_pred _ _ _ _ _).
  setoid_rewrite (hoare_pred _ _ _ _ _).
  setoid_rewrite <- pred_refines_iff_hoare_refines.
  unfold Predicative.refines; simpl.
  reflexivity.
Qed.

Theorem pred_refines_if_hoare_refines :
  forall T V (Q R : @Stmt T V), HoareWp.refines Q R -> Predicative.refines Q R.
Proof.
  intros T V Q R; intros HHrefines.
  apply pred_refines_iff_hoare_refines.
  unfold HoareWp.refines in *.
  intros Pre Post HHprepost.
  apply hoare_if_pred in HHprepost; auto.
  apply HHrefines in HHprepost.
  apply (pred_if_hoare _ _ Q); auto.
Qed.

Theorem hoare_refines_if_pred_refines :
  forall T V (Q R : @Stmt T V), Predicative.refines Q R -> HoareWp.refines Q R.
Proof.
  intros T V Q R; intros HHrefines.
  unfold HoareWp.refines; intros Pre Post HHprepost.
  apply hoare_if_pred; auto.
  constructor.
  apply pred_if_hoare in HHprepost; auto.
  pose proof (spec_inj HHprepost).
  firstorder.
Qed.

Theorem hoare_refines_iff_pred_refines :
  forall T V (Q R : @Stmt T V), HoareWp.refines Q R <-> Predicative.refines Q R.
Proof.
  intros T V Q R.
  split; intros HHrefines.
  { apply pred_refines_iff_hoare_refines.
    unfold HoareWp.refines in *.
    intros Pre Post HHprepost.
    apply hoare_pred in HHprepost; auto.
    apply (hoare_pred _ _ Q); auto.
  }
  { unfold HoareWp.refines; intros Pre Post HHprepost.
    apply hoare_pred; auto.
    apply hoare_pred in HHprepost; auto.
    constructor.
    pose proof (spec_inj HHprepost).
    firstorder.
  }
Qed.

Notation "P {{: S :}} Q" := (forall e1, (fun e => e1 = e /\ P e ) {: S :} (fun e' => Q e1 e')) (at level 50).

Lemma hoare_pred' : forall T T' (S : @Stmt T T') P Q, P {: S :} Q  <->  forall e, P e -> (exists e', pred S e e') /\ forall e', pred S e e' -> Q e'.
Proof.
  intros *.
  setoid_rewrite (hoare_pred _ _ _ _ _).
  split; intros H.
  { pose proof (@spec_inj _ _ _ _ _ H) as H'; clear H.
    firstorder.
  }
  { constructor.
    firstorder.
  }
Qed.

Lemma triple_ext_triple : forall T T' (S : @Stmt T T') (P : T -> Prop) (Q : T' -> Prop), P {{: S :}} (fun _ e' => Q e') <-> P {: S :} Q.
Proof.
  intros *.
  setoid_rewrite (hoare_pred _ _ _ _ _) at 1.
  setoid_rewrite (hoare_pred' _ _ _ _ _) at 1; simpl.
  split; intros H.
  { apply hoare_pred; constructor.
    intros e Hp.
    pose proof (H e _ (conj (eq_refl _) Hp)).
    firstorder.
  }
  { intros * (HHeq,HHp); subst e1; generalize e HHp; clear e HHp.
    apply hoare_pred'; auto.
  }
Qed.

Theorem extended_definition_iff_simple_definition : forall T V (S1 S2 : @Stmt T V),
    (forall P Q, P {: S1 :} Q -> P {: S2 :} Q)
    <-> (forall P (Q : T -> V -> Prop), (forall r, (fun s => r = s /\ P s) {: S1 :} (Q r)) -> forall r, (fun s => r = s /\ P s) {: S2 :} (Q r)).
Proof.
  intros *.
  split.
  { intros.
    apply H.
    apply H0.
  }
  { intros.
    apply triple_ext_triple.
    apply H.
    intros.
    unshelve eapply (hoare_rule_of_consequence _ _ _ _ _ _ _ _ H0); simpl; auto.
    clear; firstorder.
  }
Qed.