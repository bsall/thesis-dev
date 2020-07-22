Require Import CbC.
Unset Program Cases.

Open Scope cbc_scope.

Definition sqr n := n * n.

Program Definition SquareRoot := 
  ⟨ (fun x '(x',r')  => sqr r' <= x < sqr (1 + r') /\ x = x') ⟩ :{
      'x := (x,0,x+1); 
      ⟨fun '(x,r,h) '(x',r',h') => (sqr r <= sqr r' <= x /\ x < sqr (S r') <= sqr h) /\ x = x' ⟩  :{
        While (fun '(x,r,h) => 1 + r <> h) Do
          ⟨fun '(x,r,h) '(x',r',h') => (sqr r <= sqr r' <= x /\ x < sqr h' <= sqr h) /\ x = x' /\ (r,h) <> (r',h') ⟩  :{
             ⟨ fun '(x,r,h) '(x',r',h',m') => r < m' < h /\ x = x' /\ r = r' /\ h = h' ⟩ :{
                 '(x,r,h) := (x,r,h,r + Nat.div2 (h - r)) 
             };
             If (fun '(x,r,h,m) => sqr m <= x) Then
               '(x,r,h,m) := (x,m,h)
             Else
               '(x,r,h,m) := (x,r,m)
             End
          }
        Done 
     }; 
     '(x,r,h) := (x,r)
  }.

Require Import Div2 Even PeanoNat Lia.

Next Obligation.
  intros ((x,r),h).
  split; auto.
  set (k := div2 (h-r)).
  assert (2*r < 2*r + 2*k < 2*h).
  { rewrite <- (Nat.double_twice k).
    destruct H as ((((x',r'),h'),m'),(HH1,(HH2,(HH3,HH4)))); subst.
    destruct (even_or_odd (h'-r')).
    { subst k; rewrite <- (even_double _ H).
      lia.
    }
    { subst k; remember (h' - r'); destruct H.
      rewrite <- (even_div2 _ H), <- (even_double _ H).
      nia.
    }
  }
  lia.
Qed.
  

Next Obligation.
  intros ((x,r),h) (((x',r'),h'),HH); simpl in *.
  split.
  { intros (((xx,rx),hx),mx); simpl.
    intros [ HH1' [HH2 [HH3' HH4 ]]]; subst xx rx hx.
    assert (sqr mx <= x \/ sqr mx > x) as [ HH1 | HH1 ] by lia.
    { left; unfold sqr in *.
      split; auto; split; try lia.
      { split.
        { split; try nia. }
        { split; auto; lia. }
      }
      { split; auto.
        assert (r <> mx) by lia.
        contradict H.
        inversion H; subst; auto.
      }
    }
    { right; split; try lia.
      split; try lia.
      { unfold sqr in *. nia. }
      { split; auto.
        assert (h <> mx) by lia.
        contradict H; inversion H; subst; auto.
      }
    }
  }
  { exists (((x,r),h),r+1).
    destruct HH as (HH1,(HH2,HH3)); subst.
    repeat split; auto; try lia.
    assert (~(r = r' /\ h = h')).
    { contradict HH3; destruct HH3; subst; auto. }
    assert (r <> r' \/ h <> h') by lia.
    clear HH3 H.
    unfold sqr in *; nia.
  }
Qed.

Next Obligation.
  { apply (Wfd.by_inclusion _ _ (fun '(x',r',h') '(x,r,h)  =>
                                   r < h /\ (r < r' < h' /\ h' <= h \/ h' < h /\ r <= r' < h'))).
    { apply (Wfd.by_nat_variant _ _ (fun '(x,r,h) => h - r)).
      intros ((x,r),h) ((x',r'),h'). lia. 
    }
    { intros ((x,r),h) ((x',r'),h').
      intros (HH1,((HH21,(HH22,HH23)),HH3)).
      subst.
      assert (~(r' = r /\ h' = h)).
      { contradict HH23. firstorder. }
      assert (r' <> r \/ h' <> h) by lia.
      clear H.
      unfold sqr in *; nia. 
    }
  }
Qed.

Next Obligation.
  intros ((x,r),h) (((x',r'),h'),HH).
  unfold Wpr.wpr_spec; simpl.
  destruct HH.
  { destruct H as (HHrh,((HHsqr1,HHsqr2),(HHx,HHrh3))); subst x'.
    left; split; auto.
    split.
    { intros ((xx,rx),hx) ((HH11,HH12),(HHx,HHrhx)); subst xx.
      assert (S rx = hx \/ S rx <> hx) by lia.
      destruct H.
      { right; split; auto. }
      { left; split; auto.
        split.
        { intros ((xx',rr'),hh') HH.
          left; split; auto.
          destruct HH as ((HH21,HH22),(HHx,HHrhx')).
          subst x.
          split.
          { lia. }
          { split; auto.
            unfold not; intros.
            inversion H0; subst.
            assert (sqr rx = sqr rr') by lia.
            assert (sqr hx = sqr hh') by lia.
            clear - HHrhx' H1 H2.
            assert (rx = rr').
            { unfold sqr in *; clear HHrhx'; nia. }
            assert (hx = hh').
            { unfold sqr in *; clear HHrhx'; nia. }
            contradict HHrhx'; subst; auto.
          }
        }
        { assert (sqr (S rx) <= x \/ x < sqr (S rx)) by lia.
          destruct H0.
          { exists ((x,S rx),hx).
            split; auto.
            { split; auto.
              { clear -H0; unfold sqr in *; nia. }
              { clear -HH12; lia. }
            }
            { split; auto.
              clear; unfold not; intros.
              inversion H.
              contradict H1.
              auto.
            }
          }
          { exists ((x,rx),S rx).
            split; auto.
            { unfold sqr in *; nia. }
            { split; auto.
              clear -H; unfold not; intros.
              inversion H0.
              auto.
            }
          }
        }
      }
    }
    { exists ((x,r'),h'); split; auto. }
  }
  { destruct H.
    inversion H0; subst.
    right; split; auto.
  }
Qed.

Next Obligation.
  intros ((x,r),h) (((x',r'),h'),HH); simpl in *.
  destruct HH as ((HH1,HH2),HH3).
  assert (S r = h \/ S r <> h) by lia.
  destruct H.
  { right; split; auto; split; auto; split; auto.
    { subst; unfold sqr in *; nia. }
    { subst; lia. }
  }
  { left; split; auto.
    split.
    { intros ((xx,rx),hx); intros ((HHx',(HHprog,HHxx)),HHrh); subst x.
      destruct HHrh; subst xx.
      intros.
      split; auto.
      split; auto.
      split.
      { clear -HHprog H0; unfold sqr in *; nia. }
      { clear - HHprog HHxx H0; unfold sqr in *; nia. }
    }
    { subst.
      exists ((x',r'),S r').
      split; auto.
      unfold sqr in *.
      split; auto.
      contradict H.
      inversion H; subst.
      auto.
    }
  }
Qed.

Next Obligation.
  intros s ((x',r'),(HH,HHx)); subst x'; simpl in *.
  split; try (intros ((xx,rx),hx); intros ((HHx,HHx'),HHprog); subst); try (exists ((s,r'),S r')).
  { unfold sqr in *; simpl; split; auto.
    nia.
  }
  { split; auto.
    { unfold sqr in *.
      split.
      { nia. }
      { split.
        { nia. }
        { assert (r' <= s) by nia; clear HH; nia.
        }
      }
    }
  }
Qed.

Definition Sqrt_proof := soundness SquareRoot.
Print Assumptions Sqrt_proof.
       
Close Scope cbc_scope.