Require Import Specification Setoid.

Definition fn { T V : Type } (P : T >> V) (Q : T >> V) : T >> V :=
  fun s s' => (exists s', P s s') /\ (exists s', Q s s') /\ (P s s' \/ Q s s').

Notation "P ⊔ Q" := (fn P Q) (at level 90, right associativity, format "P  ⊔  Q").

Theorem lext : forall T U (P P' Q : T >> U), (forall s s', P s s' <-> P' s s') -> forall s s', (P ⊔ Q) s s' <-> (P' ⊔ Q) s s'.
Proof. firstorder. Qed.

Theorem rext : forall T U (P Q Q' : T >> U), (forall s s', Q s s' <-> Q' s s') -> forall s s', (P ⊔ Q) s s' <-> (P ⊔ Q') s s'.
Proof. firstorder. Qed.

Theorem ext : forall T U (P P' Q Q' : T >> U),
    (forall s s', P s s' <-> P' s s') -> (forall s s', Q s s' <-> Q' s s') -> forall s s', (P ⊔ Q) s s' <-> (P' ⊔ Q') s s'.
Proof. firstorder. Qed.

