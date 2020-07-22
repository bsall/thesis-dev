Require Import Specification Setoid.

Definition monotonic { T U : Type } (f : T >> U -> T >> U) :=
  forall (X1 X2 : T >> U), (forall s s', X1 s s' -> X2 s s') -> (forall s s', f X1 s s' -> f X2 s s').


Definition lfp { T U : Type } (f : T >> U -> T >> U) :=
  fun s s' => forall X, (forall s s', f X s s' -> X s s') -> X s s'.

Theorem lfp_extensionality : forall { T U : Type } F G, (forall (X : T >> U) s s', F X s s' <-> G X s s')
                                                  -> forall s s', lfp F s s' <-> lfp G s s'.
Proof.
  intros.
  unfold lfp.
  split; intros.
  { apply H0.
    intros; apply H1.
    rewrite <- H.
    exact H2.
  }
  { apply H0.
    intros; apply H1.
    rewrite H.
    exact H2.
  }
Qed.

Theorem f_lfp : forall { T U : Type } (f : T >> U -> T >> U)  X,
    (forall s s', f X s s' -> X s s') -> (forall s s', (lfp f) s s' -> X s s').
Proof. firstorder. Qed.

Theorem f_lfp_lfp : forall { T U : Type } (f : T >> U -> T >> U),
    (monotonic f) -> forall s s', f (lfp f) s s' -> (lfp f) s s'.
Proof.
  intros T U f HHmonotonic s s' HHf.
  unfold lfp.
  intros X HHf'.
  apply HHf'.
  apply (HHmonotonic _ _ (f_lfp _ _ HHf') _ _ HHf).
Qed.

Theorem lfp_f_lfp : forall { T U : Type } (f : T >> U -> T >> U),
    (monotonic f) -> forall s s', (lfp f) s s' -> f (lfp f) s s'.
Proof.
  intros T U f HHmonotonic s s' HHlfp.
  apply HHlfp.
  intros r r' HHf.
  apply (HHmonotonic _ _ (f_lfp_lfp _ HHmonotonic) _ _ HHf).
Qed.

Theorem lfp_fix : forall { T U : Type } (f : T >> U -> T >> U),
    (monotonic f) -> forall s s', f (lfp f) s s' <-> (lfp f) s s'.
Proof.
  intros T U f HHmonotonic s s'; split.
  { apply (f_lfp_lfp _ HHmonotonic). }
  { apply (lfp_f_lfp _ HHmonotonic). }
Qed.

Opaque lfp.