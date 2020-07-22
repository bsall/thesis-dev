(*

Definition st :=  (nat*nat*(nat-> nat)*nat)%type.
Class avantapres := { avant: st ; apres: st }.

Definition i {s:avantapres} :=
  let '(i, n, a, x) := @avant s in i.
Definition i' {s:avantapres} :=
  let '(i, n, a, x) := @apres s in i.
Definition n {s:avantapres} :=
  let '(i, n, a, x) := @avant s in n.
Definition n' {s:avantapres} :=
  let '(i, n, a, x) := @apres s in n.
Definition a {s:avantapres} :=
  let '(i, n, a, x) := @avant s in a.
Definition a' {s:avantapres} :=
  let '(i, n, a, x) := @apres s in a.
Definition x {s:avantapres} :=
  let '(i, n, a, x) := @avant s in x.
Definition x' {s:avantapres} :=
  let '(i, n, a, x) := @apres s in x.
*)

(*
Require Import List.

Import ListNotations.

Inductive Var := var : forall {T}, T -> Var.

Definition xx := var 25.

Definition type (v : Var) := match v with @var T _ => T end.

Definition val (v : Var) := match v return type v with var x => x  end.
Eval compute in (val xx).

Definition l := [var 25; var false].
Print l.
 *)

Require Import Statement ImprovedPredicative Wfd.

Open Scope stmt_scope.

Definition spec' : Stmt (nat * nat * (nat -> nat) * nat) :=
  ⟨fun '(i,n,a,x) '(i',n',a',x') => i <= n /\ a = a' /\ x = x' /\ ((forall k, i <= k < n -> a k <> x) \/ i' < n /\ a i' = x)⟩.

Definition prog' : Stmt (nat * nat * (nat -> nat) * nat) :=
  WWhile (fun '(i,n,a,x) => i <> n) Do
    IIf (fun '(i,n,a,x) => a i <> x) Then
      $(i, n, a, x) := (i + 1, n, a, x)
    Else
      $(i, n, a, x) := (i, i, a, x)                    
    End
  Done.

Theorem while_refines' : forall {T : Type} {C} {P : @Stmt T T} Kw K S,
     let Body := IIf (fun s => exists s', pred Kw s s') Then P Else Statement.Void End in
    well_founded (fun s s' => C s' /\ pred Kw s' s)
    -> (forall s s', pred Body s s' -> pred Kw s s')
    -> refines P Body
    -> (forall s s', pred K s s' <-> ((C s /\ pred_seq Body (pred K) s s') \/ (~ C s /\ s = s')))
    -> refines K S
    -> (WWhile C Do P Done ⊑ S).
Proof.
  intros T C P Kw K S Body HHwfd HHbkw HHpb HHk HHks.
  apply (refines_trans _ _ _ _ _ (While_monotonic_refines _ _ _ Body HHpb)).
  apply (refines_extensionality_left _ _ _ K).
  { apply (wfd_fix_while _ _ (pred K)); auto.
    apply (Wfd.by_inclusion _ _ _ HHwfd).
    intros s s' (HHc,HHb); split; auto.
  }
  { exact HHks. }
Qed.


Require Import Lia.

Definition spec : Stmt (nat * nat * (nat -> nat) * nat) :=
  ⟨fun '(i,n,a,x) '(i',n',a',x') => i <= n /\ i' = n' /\ (forall k, i <= k < i' -> a k <> x) /\ (i <= i' < n /\ a i' = x \/ n = n') /\ a = a' /\ x = x'⟩.

Definition prog : Stmt (nat * nat * (nat -> nat) * nat) :=
  WWhile (fun '(i,n,a,x) => i <> n) Do
    IIf (fun '(i,n,a,x) => a i <> x) Then
      $(i, n, a, x) := (i + 1, n, a, x)
    Else
      $(i, n, a, x) := (i, i, a, x)                    
    End
  Done.


Theorem correctness : prog ⊑ spec.
Proof.
  apply (while_refines' ⟨fun '(i,n,a,x) '(i',n',a',x') => i < i' <= n /\ n' = n \/ i < n /\ n' = i /\ i' = i⟩ spec).
  { apply (Wfd.by_variant _ _ _ (fun '(i,n,a,x) => n - i) _ Wf_nat.lt_wf).
    intros (((i',n'),a'),x') (((i,n),a),x); simpl. lia.
  }
  { intros (((i,n),a),x) (((i',n'),a'),x'); simpl.
    intros [(((((j',m'),b'),y'),HH1),HHeq) | (_,HHfalse)].
    { destruct HHeq as [(_,HHeq) | (_,HHeq) ]; inversion HHeq; clear HHeq; subst i' n' a' x'.
      all : lia.
    }
    { contradiction. }
  } 
  { firstorder. }
  { intros  (((i,n),a),x) (((i',n'),a'),x'); simpl; split.
    { intros (HHin,(HHi'n',(HHspec,(HH,(HHa,HHx))))).
      { subst x' a'.
        apply Lt.le_lt_or_eq in HHin.
        destruct HHin.
        { left; split.
          { lia. }
          { left; split.
            { exists (n,n,a,x); left; lia. }
            { assert (i = i' \/ i < i') by lia.
              destruct H0.
              { subst i' n'.
                destruct HH.
                { destruct H0; right.
                  repeat split; auto.
                }
                { subst i; lia. }
              }
              { left; split.
                { apply HHspec; lia. }
                { repeat split; auto.
                  { lia. }
                  { intros k HHk; apply HHspec. lia. }
                  { lia. }
                }
              }
            }
          }
        }
        { right; split; auto.
          subst i' i.
          destruct HH.
          { lia. }
          { subst n'; auto. }
        }
      }
    }
    { intros.
      destruct H.
      { destruct H.
        destruct H0 as [ (((((i'',n''),_),_),HH),[ (HHaix,(HHin,(HHi'n',(HHspec,(HHend,(HHa,HHx))))))
                                                 | (HHaix,(_,(HHi'n',(HHspec,(HHend,(HHa,HHx)))))) ]) | (_,HHfalse) ]
        ; try contradiction.
        { repeat split; auto.
          { lia. }
          { intros k HHk.
            assert (i = k \/ i + 1 <= k) by lia.
            destruct H0.
            { subst k; auto. }
            { apply HHspec; lia. }
          }
          { subst a' x'.
            destruct HHend; auto.
            destruct H0.
            left; split; auto.
            lia.
          }
        }
        { subst a' x' i'.
          destruct HHend.
          { lia. }
          { subst n'.
            repeat split; auto.
            { lia. }
            { left; split; lia. }
          }
        }
      }
      { destruct H.
        inversion H0; subst i' n' a' x'; clear H0.
        repeat split; auto; try lia.
        intros k HHk; lia.
      }
    }
  }
  { apply refines_reflexive. }
Qed.

(* 
 Definition spec  :=
  fun {_:avantapres} => i <= n /\ i' = n' /\ (forall k, i <= k < i' -> a k <> x) /\ (i <= i' < n /\ a i' = x \/ n = n') /\ a = a' /\ x = x'.

 Definition spec : Stmt st :=
  ⟨fun '(mk_st i n a x) '(mk_st i' n' a' x') => i <= n /\ i' = n' /\ (forall k, i <= k < i' -> a k <> x) /\ (i <= i' < n /\ a i' = x \/ n = n') /\ a = a' /\ x = x'⟩.
(x at l)
  let i = (i @ s) in
  let i' = (i @ s') in
  
*)

Close Scope stmt_scope.