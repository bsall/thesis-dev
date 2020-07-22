Require Import Setoid.

Require Import LeastFixpoint Wfd AngelicComposition.

Definition ftcl { T : Type } (R : T -> T -> Prop) X := (fun s s' => (X ⊡ R) s s' \/ R s s').

Theorem ftcl_monotonic : forall T R (X Y : T -> T -> Prop) , (forall s s', X s s' -> Y s s') -> forall s s', ftcl R X s s' -> ftcl R Y s s' .
Proof. firstorder. Qed.

Definition tcl { T : Type } (R : T -> T -> Prop) := lfp (ftcl R).

Theorem tcl_fix : forall { T : Type } (R : T -> T -> Prop), forall s s', tcl R s s' <-> (tcl R ⊡ R) s s' \/ R s s'.
Proof.
  intros *.
  unfold tcl.
  setoid_rewrite (lfp_fix (ftcl R) (ftcl_monotonic _ R)).
  reflexivity.
Qed.

Theorem tcl_rotate : forall { T : Type } (R : T -> T -> Prop), forall s s', (R ⊡ tcl R) s s' <-> (tcl R ⊡ R) s s'.
Proof.
  intros *.
  split.
  { intros * (sx,(HH1,HH2)).
    generalize s HH1; clear s HH1.
    pattern sx,s'.
    apply HH2; clear sx s' HH2.
    intros.
    unfold ftcl in H.
    destruct H.
    { destruct H as (x,(H,H')).
      exists x; split; auto.
      apply tcl_fix; auto.
    }
    { exists s; split; auto.
      apply tcl_fix; auto.
    }
  }
  { intros (sx,(HHtcl,HH)).
    generalize s' HH; clear s' HH.
    pattern s,sx; apply HHtcl; clear s sx HHtcl.
    intros * [ HH | HH ].
    { destruct HH as (x,(HH1,HH2)).
      intros.
      destruct (HH1 _ HH2) as (y,(HH3,HH4)).
      exists y; split; auto.
      apply tcl_fix; left; exists s'; auto.
    }
    { intros.
      exists s'; split; auto.
      apply tcl_fix; auto.
    }
  }
Qed.

Theorem tcl_trans :  forall { T : Type } (R : T -> T -> Prop), forall s s', (tcl R ⊡ tcl R) s s' -> tcl R s s'.
Proof.
  intros * (sx,(HHtcl1,HHtcl2)).
  generalize s HHtcl1; clear s HHtcl1.
  pattern sx,s'.
  apply HHtcl2; clear sx s' HHtcl2.
  intros.
  unfold ftcl in H.
  apply tcl_fix; left.
  destruct H.
  { destruct H as (sx,(HH1,HH2)).
    apply HH1 in HHtcl1.
    exists sx; auto.
  }
  { exists s; auto. }
Qed.

Theorem tcl_inv : forall T (R : T -> T -> Prop), forall s s', tcl (fun s s' => R s' s) s s' <-> tcl R s' s.
Proof.
  intros*.
  split.
  { intros HHtcl.
    pattern s,s'; apply HHtcl; clear s s' HHtcl.
    intros * HHtcl.
    unfold ftcl in HHtcl.
    destruct HHtcl.
    { destruct H as (x,(H1,H2)).
      assert ((R ⊡ tcl R) s' s) by firstorder; clear H1 H2.
      rewrite tcl_rotate in H.
      apply tcl_fix.
      auto.
    }
    { apply tcl_fix; auto. }
  }
  { intros H.
    pattern s',s; apply H; clear s' s H.
    intros.
    destruct H.
    { destruct H as (x,(H1,H2)).
      assert (((fun s s' => R s' s) ⊡ tcl (fun s s' => R s' s)) s' s) by firstorder; clear H1 H2.
      rewrite tcl_rotate in H.
      apply tcl_fix.
      auto.
    }
    { apply tcl_fix; auto. }
  }
Qed.

Theorem tcl_wfd : forall T (R : T -> T -> Prop), well_founded R <-> well_founded (tcl R).
Proof.
  split; intros.
  { apply (Wfd.by_simulation _ _ _ (fun s s' => ((tcl R) s s' \/ s = s')) R); auto.
    { intros x _; exists x; auto. }
    { intros * HH.
      rewrite rdistr_or, <- (rneutral_eq _ _ (tcl R)) in HH.
      rewrite ldistr_or, <- (lneutral_eq _ _ R).
      rewrite <- tcl_fix.
      destruct HH; auto.
      apply (tcl_trans _ _ _ H0).
    }
  }
  { apply (Wfd.by_inclusion _ _ _ H).
    intros x y; rewrite tcl_fix.
    auto.
  }
Qed.

Theorem tcl_dom : forall T (R : T -> T -> Prop) s, (exists s', R s s') <-> (exists s', tcl R s s').
Proof.
  intros *.
  split.
  { intros (s',HHr).
    exists s'; rewrite tcl_fix.
    auto.
  }
  { intros (s',HHtcl).
    pattern s,s'.
    apply HHtcl.
    clear HHtcl s s'.
    intros.
    destruct H.
    { destruct H as (_,(H',_)). auto. }
    { eauto. }
  }
Qed.

Theorem tcl_ran : forall T (R : T -> T -> Prop) s', (exists s, R s s') <-> (exists s, tcl R s s').
Proof.
  intros *.
  split.
  { intros (s,HHr).
    exists s; rewrite tcl_fix.
    auto.
  }
  { intros (s,HHtcl).
    pattern s,s'.
    apply HHtcl.
    clear HHtcl s s'.
    intros.
    destruct H.
    { destruct H as (k,(_,H'')). eauto. }
    { eauto. }
  }
Qed.


Definition frtcl { T : Type } (R : T -> T -> Prop) X := (fun s s' => (R ⊡ X) s s' \/ s = s').

Theorem frtcl_monotonic : forall T R (X Y : T -> T -> Prop) , (forall s s', X s s' -> Y s s') -> forall s s', frtcl R X s s' -> frtcl R Y s s' .
Proof. firstorder. Qed.

Definition rtcl { T : Type } (R : T -> T -> Prop) := lfp (frtcl R).

Theorem rtcl_fix : forall { T : Type } (R : T -> T -> Prop), forall s s', rtcl R s s' <-> (R ⊡ rtcl R) s s' \/ s = s'.
Proof.
  intros *.
  unfold tcl.
  setoid_rewrite (lfp_fix (frtcl R) (frtcl_monotonic _ R)).
  reflexivity.
Qed.

Definition reflexive { T } (R : T -> T -> Prop) := forall x, R x x.
Definition irreflexive { T } (R : T -> T -> Prop) := forall x, ~ R x x.
Definition transitive { T } (R : T -> T -> Prop) := forall x y z, R x y -> R y z -> R x z.

Theorem rtcl_trans : forall T (R : T -> T -> Prop), transitive (rtcl R).
Proof.
  unfold transitive; intros * HHr.
  generalize z; clear z.
  apply HHr.
  simpl in *; intros.
  destruct H.
  { destruct H.
    destruct H.
    apply rtcl_fix; left.
    exists x0; firstorder.
  }
  { subst s'; auto. }
Qed.


Theorem rtcl_least_trans : forall T (R S : T -> T -> Prop),
    reflexive S
    -> transitive S
    -> (forall s s', R s s' -> S s s')
    -> forall s s', rtcl R s s' -> S s s'.
Proof.
  intros.
  apply H2.
  intros.
  destruct H3.
  { destruct H3.
    destruct H3.
    apply H1 in H3.
    apply (H0 _ _ _ H3 H4).
  }
  { subst s'0; apply H. }
Qed.

Theorem trans_rtcl : forall T (R : T-> T -> Prop), transitive R -> forall s s', R s s' \/ s = s' <-> rtcl R s s'.
Proof.
  intros.
  split.
  { intros.
    destruct H0.
    { rewrite rtcl_fix.
      left; unfold "⊡".
      setoid_rewrite rtcl_fix.
      exists s'; firstorder.
    }
    { subst; apply rtcl_fix; right; auto. }
  }
  { apply (rtcl_least_trans _ _ (fun s s' => R s s' \/ s = s')); auto.
    { firstorder. }
    { unfold transitive in *.
      intros.
      destruct H0; subst; destruct H1; subst.
      { left; apply (H _ _ _ H0 H1). }
      { left; auto. }
      { left; auto. }
      { right; auto. }
    }
  }
Qed.

Theorem wfd_by_quasi_commutativity :
  forall (T : Type) (R S : T -> T -> Prop),
    well_founded R
 -> well_founded S
 -> (forall x y z, R x y -> S y z -> (S ⊡ R) x z \/ R x z \/ S x z)
 -> well_founded (fun s s' => R s s' \/ S s s').
Proof.
  intros.
  (* apply tcl_wfd in H. *)
  apply tcl_wfd in H0. 
  intros a.
  apply (well_founded_ind H).
  intros x; pattern x.
  apply (well_founded_ind H0).
  clear a x; intros.
  constructor.
  intros.
  destruct H4; auto.
  apply H2.
  { apply tcl_fix; auto. }
  intros.
  generalize x y H2 H3 H4 H5; clear x y H2 H3 H4 H5.
  pattern y0; apply (well_founded_ind H).
  intros.
  destruct (H1 _ _ _ H6 H5).
  { destruct H7 as (z,(H7,H8)).
    pose proof (H4 _ H8).
    destruct H9.
    apply H9.
    auto.
  }
  { destruct H7; auto.
    apply H3.
    { apply tcl_fix; auto. }
    { intros.
      apply H2 with (x := x0) (y0 := x); auto.
    }
  }
Qed.
