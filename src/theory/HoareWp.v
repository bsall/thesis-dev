Require Import Decidable.

Require Import Effect Predicate Specification Statement Wfd.

Inductive ValidHoareTriple { T } : forall { U : Type}, @Predicate T -> @Stmt T U -> @Predicate U -> Prop :=
| Void : forall U (P : @Predicate T) (Q : @Predicate U) , (forall s, ~ P s) -> ValidHoareTriple P Void Q
                                                                        
| Assignment :
    forall { U } (effect : @Effect T U) (P Q : Predicate),
      (forall s, P s -> Q (effect s))
      -> ValidHoareTriple P (Assignment effect) Q

| Seq :
    forall  { Tx U } P R Q (S1 : @Stmt T Tx) (S2 : @Stmt Tx U),
    @ValidHoareTriple _ _ P S1 Q
    -> @ValidHoareTriple _ _  Q S2 R
    -> @ValidHoareTriple T U P (Statement.Seq S1 S2) R

| If :
    forall { U } (P : @Predicate T) (Q : @Predicate U) (C : @Predicate T)(St Sf : @Stmt T U),
      (forall s, P s -> decidable (C s))
    -> ValidHoareTriple (fun s => C s /\ P s) St Q
    -> ValidHoareTriple (fun s => ~ C s /\ P s) Sf Q
    -> ValidHoareTriple P (If C St Sf) Q

 | While :
    forall (W : Type) (P : @Predicate T) (Q : @Predicate T) (I : @Predicate T) (C : @Predicate T)(B : @Stmt T T)(R : W -> W -> Prop)(V : T -> W),
      (forall s, I s -> decidable (C s))
      -> well_founded R
      -> (forall s, P s -> I s)
      -> (forall v, @ValidHoareTriple T T (fun s => C s /\ I s /\ v = V s) B (fun s => I s /\ R (V s) v))
      -> (forall s, ~ C s -> I s -> Q s)
      -> ValidHoareTriple P (While C B) Q

| Spec :
    forall { U } (P Q : Predicate) (spec : T >> U),
    (forall s , P s -> (forall s', spec s s' -> Q s') /\ (exists s', spec s s'))
    -> ValidHoareTriple P (Spec spec) Q

| Guarded :
    forall { U } (P : @Predicate T) (Q : @Predicate U) (C : @Predicate T)(S : @Stmt T U),
    (forall s, P s -> C s)
    -> ValidHoareTriple (fun s => C s /\ P s) S Q
    -> ValidHoareTriple P (WWhen C Then S End) Q

| Choice :
    forall { U } (P : @Predicate T) (Q : @Predicate U)(St Sf : @Stmt T U),
      ValidHoareTriple P St Q
    -> ValidHoareTriple P Sf Q
    -> ValidHoareTriple P (St ⫾ Sf) Q.

Lemma spec_inj : forall {T U : Type} {R : T >> U} {P Q},
    ValidHoareTriple P (Statement.Spec R) Q
    -> (forall s , P s -> (forall s', R s s' -> Q s') /\ (exists s', R s s')).
Proof.
  Set Printing Implicit.
  intros * HHtriple.
  remember (Statement.Spec R) as S.
  destruct HHtriple; try discriminate; subst.
  apply stmt_spec_inj in HeqS; subst.
  auto.
Qed.

Notation "P {: C :} Q" := (ValidHoareTriple P C Q) (at level 50, format "P  {:  C  :}  Q").

(* (refines S1 S2) is the proposition : S1 refines S2 *)
(* S1 refines S2 iff every specification satisfied by S2 is also satisfied by S1, i.e. S1 can safely replace S2 in all contexts *)
Definition refines { T U : Type } (S1 S2 : @Stmt T U) := forall P Q, P {: S2 :} Q -> P {: S1 :} Q.

Notation "C1 ⊑ C2" := (refines C1 C2) (at level 60, format "C1  ⊑  C2").