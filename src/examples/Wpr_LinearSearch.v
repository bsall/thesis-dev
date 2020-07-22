Require Import Statement Wpr Wfd.

Require Import Lia.

Arguments wpr_while : simpl never.

Open Scope stmt_scope.

Definition spec : @Stmt (nat * nat * (nat -> nat) * nat)  (nat * nat * (nat -> nat) * nat) :=
  ⟨fun '(i,n,a,x) '(i',n',a',x') => ((forall k, k < n -> a k <> x) \/ i' < n /\ a i' = x) /\ a = a' /\ x = x'⟩.

Definition prog : @Stmt (nat * nat * (nat -> nat) * nat) (nat * nat * (nat -> nat) * nat) :=
  $(i, n, a, x) := (0, n, a, x);
  WWhile (fun '(i,n,a,x) => i <> n) Do
    IIf (fun '(i,n,a,x) => a i <> x) Then
      $(i, n, a, x) := (i + 1, n, a, x)
    Else
      $(i, n, a, x) := (i, i, a, x)                    
    End
  Done.

Theorem correctness : prog ⊑ spec.
Proof. {
  unfold prog.
  match goal with |- @refines ?T ?V (?P1;WWhile ?C Do ?Q Done) _ =>
                  set (P := ⟨ fun '(i, n, a, x) '(i', n', a', x') => i < n /\ a' = a /\ x' = x /\
                                    (i < i' <= n /\ (forall k, i <= k < i' -> a k <> x) /\ n = n' \/ i' < n /\ a i' = x /\ n' = i')⟩ : @Stmt T V);
                    assert (WWhile C Do Q Done ⊑ WWhile C Do P Done) end.
  { apply While_monotonic_refines.
    unfold refines; intros (((i,n),a),x) ((((j,m),b),y),HH); simpl in HH.
    simpl.
    assert (a i = x \/ a i <> x) as [ HHax | HHax ] by lia.
    { right; split; auto.
      split.
      { clear - HH; lia. }
      { split; auto; split; auto; right.
        split; auto. lia.
      }
    }
    { left; split; auto.
      split.
      { clear -HH; lia. }
      { split; auto; split; auto.
        left; split.
        { clear -HH; lia. }
        { split; auto.
          intros k HHk.
          assert (k = i) by (clear -HHk; lia).
          rewrite H; auto.
        }
      }
    }
  }
  { apply (refines_trans _ _ _ _ _ (Seq_right_monotonic_refines _ _ _ _ _ _ H)).
    clear H.
    match goal with |- @refines ?T ?V (_;(WWhile ?C Do ?Q Done)) _ => epose proof (wfd_while_refines_if C P _ _) end.
    apply (refines_trans _ _ _ _ _ (Seq_right_monotonic_refines _ _ _ _ _ _ H)).
    intros (((i,n),a),x) ((((j,m),b),y),HH); simpl in HH.
    simpl.
    unfold wpr_spec; simpl.
    assert (n = 0 \/ n <> 0) as [HHn0 | HHn0] by lia.
    { right; subst n.
      repeat (match goal with |- _ /\ _ => split end); auto.
      left; intros k HHk. clear -HHk; lia.
    }
    { left; split; auto.
      split.
      { intros (((i',n'),a'),x') ((_,(HHa,(HHx,HHind))),HH2).
        subst a' x'; split; auto.
        assert (i' = n') by (clear -HH2; lia); subst i'; clear HH2.
        destruct HHind as [ (HHn'n,(HHak,HHnn')) | (HHn'n,(HHan',_)) ]; auto.
        subst n'; left; intros k HHk.
        apply HHak; clear -HHk; lia.
      }
      {  destruct HH as ([ HHnotfound | (HHj1,HHj2) ],_).
         { exists (n,n,a,x); split; auto.
           split.
           { clear -HHn0; lia. }
           { split; auto; split; auto; left.
             split.
             { clear -HHn0; lia. }
             { split; auto; intros k HHk.
               apply HHnotfound; clear -HHk; lia.
             }
           }
         }
         { exists (j,j,a,x); split; auto.
           split.
           { clear - HHn0; lia. }
           { split; auto. }
         }
      }
    }
  }
  Unshelve.
  { simpl.
    clear.
    apply (Wfd.by_inclusion _ _ (fun '(i',n',a',x') '(i,n,a,x)  => i < i' <= n /\ n = n' \/ i < n /\ i = i' /\ n' = i)).
    { apply (Wfd.by_nat_variant _ _ (fun '(i,n,a,x) => n - i)).
      intros (((i,n),a),x) (((j,m),b),y) H.
      lia.
    }
    { intros (((i,n),a),x) (((j,m),b),y) H.
      repeat (match goal with [ H : _ /\ _  |- _ ] => destruct H | [ H : _ \/ _ |- _ ] => destruct H end); subst n.
      { lia. }
      { clear -H1; lia. }
    }
  }
  { intros (((i,n),a),x).
    split.
    { intros (((i',n'),a'),x'); simpl.
      intros (HHin1,(HHin,(HHa,(HHx,HH)))); subst a' x'.
      split.
      { intros (((ix,nx),ax),xx); simpl.
        intros [(_,(HHi'n',(HHa,(HHx,HH2)))) | (HH11,HH12) ].
        { subst ax x.
          split; auto; split; auto; split; auto; split; auto.
          destruct HH as [ (HHii',(HHak,HHnn')) | (_,(_,HHi'n'2)) ]; subst n'.
          { destruct HH2 as [ (HHx1,(HHx2,HHx3)) | HHx ].
            { subst nx.
              left; split; try lia.
              split; auto.
              intros k HHk.
              assert (k < i' \/ i' <= k) by lia.
              destruct H0.
              { apply HHak; lia. }
              { apply HHx2; lia. }
            }
            { right; auto. }
          }
          { clear -HHi'n'; lia. }
        }
        { inversion HH12; subst ix nx ax xx; clear HH12.
          split; auto.
        }
      }
      { assert (i' = n' \/ i' <> n') by lia.
        destruct H0.
        { subst n'; exists (i',i',a,x); auto. }
        { destruct HH. 
          { assert (a i' = x \/ a i' <> x) by lia.
            destruct H2.
            { exists (i',i',a,x); left; split; auto.
              split.
              { lia. }
              { split; auto; split; auto; right; split; auto. lia. }
            }
            { exists (i' + 1, n', a, x).
              left; split; auto; split.
              { lia. } 
              { split; auto; split; auto; left; split.
                { lia. }
                { split; auto. 
                  clear -H2; intros k HHk.
                  assert (k = i') by lia; subst k; auto.
                }
              }
            }
          }
          { destruct H1 as (_,(_,H1)).
            subst i'. contradict H0; auto.
          }
        }
      }
    }
    { auto. }
  }
} Qed.

Close Scope stmt_scope.
