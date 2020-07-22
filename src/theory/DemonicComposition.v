Require Import Specification DemonicJoin  Setoid.

Definition fn { T U V : Type } (P : T >> U) (Q : U >> V) : T >> V :=
  fun s s' => (exists sx, P s sx /\ Q sx s') /\ (forall sx, P s sx -> exists s', Q sx s').

Notation "P ⊟ Q" := (fn P Q) (at level 90, right associativity, format "P  ⊟  Q").

Theorem thm : forall T (C : T -> Prop)(P : T >> T) (Q : T >> T),
    ( forall s sx : T, C s /\ P s sx -> exists s'0 : T, C sx /\ P sx s'0 \/ ~ C sx /\ sx = s'0)
    -> forall s s', ((fun s s' => C s /\ P s s') ⊟ (fun s s' => C s /\ P s s' \/ ~ C s /\ s = s')) s s'
            <-> (((fun s s' => C s /\ P s s' /\ C s') ⊟ (fun s s' => C s /\ P s s')) s s' \/ ((fun s s' => C s /\ P s s'/\ ~ C s') ⊟ (fun s s' => ~ C s /\ s = s')) s s').
Proof.
  intros.
  split; intros.
  {  destruct H0 as ((sx,(HH11,HH12)),HH2).
     destruct HH12.
     { left; firstorder. }
     { destruct H0.
       subst sx.
       clear HH2.
       right.
       firstorder.
     }
  }
  { split.
    { firstorder. }
    { firstorder. }
  }
Qed.

Theorem assoc : forall { T U V W : Type } (P : T >> U) (Q : U >> V) (R : V >> W) s s', (P ⊟ Q ⊟ R) s s' <-> ((P ⊟ Q) ⊟ R) s s'.
Proof.
  intros T U V W P Q R s s'.
  split.
  { intros ((sx,(HHp,((sy,(HHq,HHr)),HHqr))),HHpqr).
    split.
    { exists sy; split; auto.
      firstorder.
    }
    { firstorder. }
  }
  { intros ((sy,(((sx,(HHp,HHq)),HHpq),HHr)),HHpqr).
    split.
    { exists sx; split; auto.
      firstorder.
    }
    { intros sz HHp'.
      destruct (HHpq _ HHp') as (sz',HHq').
      destruct (HHpqr sz') as (sz'',HHr').
      { firstorder. }
      { exists sz''; firstorder. }
    }
  }
Qed.

Theorem right_monotonic : forall (T U V : Type) (P : T >> U) (Q1 Q2 : U >> V),
    (forall s s', Q1 s s' -> Q2 s s') -> (forall s s', (P ⊟ Q1) s s' -> (P ⊟ Q2) s s').
Proof.
  intros T U V P Q1 Q2 HHq1q2 s s' ((sx,(HHpq1,HHpq1')),HHpq1'').
  split.
  { destruct (HHpq1'' _ HHpq1) as (sx',HHq1).
    exists sx; split; auto.
  }
  { intros sy HHp.
    destruct (HHpq1'' _ HHp) as (sy',HHq1).
    exists sy'; auto.
  }
Qed.

Theorem left_extensionality : forall { T U V : Type } (P1 P2 : T >> U) (Q : U >> V),
    (forall s s', P1 s s' <-> P2 s s') -> (forall s s', (P1 ⊟ Q) s s' <-> (P2 ⊟ Q) s s').
Proof. firstorder. Qed.

Theorem right_extensionality : forall { T U V : Type } (P : T >> U) (Q1 Q2 : U >> V),
    (forall s s', Q1 s s' <-> Q2 s s') -> (forall s s', (P ⊟ Q1) s s' <-> (P ⊟ Q2) s s').
Proof.
  intros.
  split; apply right_monotonic; firstorder.
Qed.

Theorem extensionality : forall { T U V : Type } (P1 P2 : T >> U) (Q1 Q2 : U >> V),
    (forall s s', P1 s s' <-> P2 s s') -> (forall s s', Q1 s s' <-> Q2 s s') -> (forall s s', (P1 ⊟ Q1) s s' <-> (P2 ⊟ Q2) s s').
Proof.
  intros; split; intros HH.
  { rewrite (left_extensionality _ _ _ H) in HH.
    rewrite (right_extensionality _ _ _ H0) in HH.
    auto.
  }
  { rewrite (left_extensionality _ _ _ H).
    rewrite (right_extensionality _ _ _ H0).
    auto.
  }
Qed.

Theorem left_identity_neutrality : forall { T U : Type } (Q : T >> U), (forall s s', ((fun s s' => s = s') ⊟ Q) s s' <-> Q s s').
Proof.
  split.
  { intros ((sx,(HH11,HH12)),HH2).
    subst sx; firstorder.
  }
  { intros; split.
    { eauto. }
    { intros sx HH; subst sx; eauto. }
  }
Qed.

Theorem right_identity_neutrality : forall { T U : Type } (Q : T >> U), (forall s s', (Q ⊟ (fun s s' => s = s')) s s' <-> Q s s').
Proof.
  split.
  { intros ((sx,(HH11,HH12)),HH2).
    subst sx; firstorder.
  }
  { intros; split; eauto. }
Qed.

Theorem ldistr_join : forall T U V (P Q : T >> U) (R : U >> V), forall s s', ((P ⊔ Q) ⊟ R) s s' <-> ((P ⊟ R) ⊔ (Q ⊟ R)) s s'.
Proof.
  unfold "⊟"; firstorder.
  { exists s'.
    split; eauto.
    intros; apply H0.
    firstorder.
  }
  { destruct (H0 x1).
    { firstorder. }
    { exists x2; split; eauto.
      firstorder.
    }
  }
  { destruct (H0 x0).
    { firstorder. }
    { exists x2; split; eauto.
      firstorder.
    }
  }
  { exists s'.
    split; eauto.
    intros; apply H0.
    firstorder.
  }
Qed.

Theorem rdistr_join : forall T U V (R : T >> U) (P Q : U >> V), forall s s', (R ⊟ (P ⊔ Q)) s s' <-> ((R ⊟ P) ⊔ (R ⊟ Q)) s s'.
Proof.
  unfold "⊟"; firstorder.
Qed.
