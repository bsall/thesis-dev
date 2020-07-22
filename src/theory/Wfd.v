Require Import Arith.Wf_nat.

Require Import AngelicComposition.

Theorem by_inclusion :
  forall (T : Type) (R1 R2 : T -> T -> Prop),
    well_founded R2
    -> (forall x y, R1 x y -> R2 x y)
    -> well_founded R1.
Proof.
  intros.
  unfold well_founded; intros.
  pattern a.
  apply (well_founded_ind H).
  intros.
  constructor; intros.
  apply H1.
  auto.
Qed.

Theorem by_extensionality : forall T (R S : T -> T -> Prop), (forall s s', R s s' <-> S s s') -> well_founded R <-> well_founded S.
Proof.
  intros.
  split; intros H1; apply (by_inclusion _ _ _ H1); firstorder.
Qed.

Theorem by_variant :
  forall (T1 T2 : Type) (R : T1 -> T1 -> Prop) (f : T1 -> T2) W,
    well_founded W
    -> (forall x y, R x y -> W (f x) (f y))
    -> well_founded R.
Proof.
  intros T1 T2 R f W HHwfd HHsim.
  intros t1'.
  constructor; intros t1 HHr.
  generalize t1 (HHsim _ _ HHr).
  pattern (f t1'); apply (well_founded_ind HHwfd).
  intros t2' HHind u1 HHw.
  constructor; intros v1 HHrv.
  apply (HHind (f u1)); auto.
Qed.


Theorem by_simulation :
  forall (T1 T2 : Type) (R : T1 -> T1 -> Prop) (S : T1 -> T2 -> Prop) (W : T2 -> T2 -> Prop),
    (forall x, (exists y, R y x) -> exists y, S x y)
    -> well_founded W
    -> (forall x z, (R ⊡ S) x z -> (S ⊡ W) x z)
    -> well_founded R.
Proof.
  intros T1 T2 R S W HHsurj HHwfd HHsim. 
  intros t1'.
  constructor; intros t1 HHr.  
  destruct (HHsurj t1') as (s1,HHs1); eauto.
  generalize t1 t1' HHr HHs1; clear t1 t1' HHs1 HHr.
  pattern s1; apply (well_founded_ind HHwfd).
  intros. 
  constructor; intros.
  destruct (HHsurj t1) as (s1',HHs1'); eauto.
  destruct (HHsim _ _ (ex_intro _ _ (conj HHr HHs1))) as (s1'',HHws).
  destruct HHws.
  eapply H; eauto.
Qed.

Theorem by_functional_simulation :
  forall (T1 T2 : Type) (R : T1 -> T1 -> Prop) (S : T1 -> T2) (W : T2 -> T2 -> Prop),
    well_founded W
    -> (forall x y, R x y -> W (S x) (S y))
    -> well_founded R.
Proof.
  intros.
  apply (by_simulation _ _ _ (fun x y => y = S x) W).
  { intros x _; eauto. }
  { exact H. }
  { intros; unfold "⊡" in *.
    clear - H0 H1.
    destruct H1 as (sx,(H11,H12)); subst.
    eauto.
  }
Qed.

Theorem by_direct_functional_simulation :
  forall (T1 T2 : Type) (S : T1 -> T2) (W : T2 -> T2 -> Prop),
    well_founded W
    -> well_founded (fun x y => W (S x) (S y)).
Proof.
  intros.
  apply (by_functional_simulation _ _ _ S W H).
  clear; auto.
Qed.
  
Theorem by_nat_variant :
  forall (T1 : Type) (R : T1 -> T1 -> Prop) (f : T1 -> nat),
    (forall x y, R x y -> f x < f y) -> well_founded R.
Proof. intros *. apply (by_variant _ _ _ _ _ lt_wf). Qed.

