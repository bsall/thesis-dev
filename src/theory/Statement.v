Require Import Effect Predicate Specification.

Inductive Stmt { T } : Type -> Type :=
| Void { V } : @Stmt T V 
| Assignment { V } : @Effect T V -> @Stmt T V
| Seq : forall { U V }, @Stmt T U -> @Stmt U V -> @Stmt T V
| If { V } : @Predicate T -> @Stmt T V -> @Stmt T V -> @Stmt T V 
| While : @Predicate T -> @Stmt T T -> @Stmt T T
| Spec { V } : @Specification T V -> @Stmt T V
| Guarded { V } : @Predicate T -> @Stmt T V -> @Stmt T V
| Choice { V } : @Stmt T V -> @Stmt T V -> @Stmt T V.

Definition Skip { T } := Assignment (fun (s : T) => s).

Definition abort { T T' } := Spec (fun (s : T) (s' : T') => False).

Lemma stmt_spec_inj : forall T V (S1 S2 : T >> V), Spec S1 = Spec S2 -> S1 = S2.
Proof.
  refine (fun T V (S1 S2 : T >> V)(H : Spec S1 = Spec S2) =>
            f_equal (fun s => match s with | Spec SS => SS | _ => fun s s' => False end) H).
Qed.

Notation "$ x := y" := (Assignment (fun 'x => y)) (at level 50, x pattern, format "$ x  :=  y") : stmt_scope.
Notation "x ; y" := (Seq x y) (at level 51, format "'[v' x ; '/' y ']'", right associativity) : stmt_scope.
Notation "'IIf' c 'Then' p 'Else' q 'End'" :=
  (If c p q) (at level 52, format "'[v' IIf  c   Then '/'  p '/' Else '/'  q '/' End ']'") : stmt_scope.
Notation "'IIf' c 'Then' p 'End'" :=
  (If c p Skip) (at level 52, format "'[v' IIf  c  Then  p  End ']'") : stmt_scope.
Notation "'WWhile' c 'Do' p 'Done'" :=
  (While c p) (at level 52, format "'[v' WWhile  c  Do '/'  p '/' Done ']'") : stmt_scope.
Notation "⟨ x ⟩" := (Spec x) (at level 0, format "⟨ x ⟩") : stmt_scope.
Notation "'WWhen' c 'Then' p 'End'" :=
  (Guarded c p) (at level 52, format "'[v' WWhen  c  Then '/'  p '/' End ']'") : stmt_scope.
Notation "x ⫾ y" := (Choice x y) (at level 51, format "'[v' x ⫾ '/' y ']'", right associativity) : stmt_scope.

Bind Scope stmt_scope with Stmt. 