From Imp Require Export header_extensible.
From Stdlib Require Import Lia.

Section exp_lam.
    Variable exp : Type.

    Inductive exp_lam : Type := 
        | ab : exp -> exp_lam
        | app : exp -> exp -> exp_lam
        | bvar : nat -> exp_lam
    .

    Context `{retract exp_lam exp}.

    Definition ab_  (s0 : exp  ) : _ := inj (ab s0).
    Definition app_  (s0 s1 : exp  ) : _ := inj (app s0 s1).
    Definition bvar_  (n : nat) : _ := inj (bvar n).

    Variable open_rec : nat -> exp -> exp -> exp.

    Definition open_rec_lam (k : nat) (u : exp) (e : exp_lam) : exp := 
        match e with 
            | bvar n => if Nat.eqb k n then u else bvar_ n
            | app t t'   => app_ (open_rec k u t) (open_rec k u t')
            | ab t       => ab_ (open_rec (S k) u t)
        end.

    Variable retract_open_rec : forall (n : nat) s (e : exp_lam),
            open_rec n s (inj e) = open_rec_lam n s e.

    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc : forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.

    Inductive lc'_lam : nat -> exp -> Prop := 
        | lc_app  n t t' : lc' n t -> lc' n t' -> lc'_lam n (app_ t t')
        | lc_ab   n t    : lc' (S n) t  -> lc'_lam n (ab_ t)
        | lc_bvar k n    : k < n -> lc'_lam n (bvar_ k)
    .

    Variable retract_lc: forall n e, lc'_lam n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_lam n (inj e).

    Lemma nat_shenenigans : forall n m, n < S m -> n = m \/ n < m.
    Proof. 
        intros n. 
        induction n.
        - intros m. destruct m. {left. easy. } right. apply PeanoNat.Nat.lt_0_succ.
        - intros m H'. apply PeanoNat.lt_S_n in H'.
          destruct m. {apply PeanoNat.Nat.nlt_0_r in H'. exfalso. easy. }
          apply IHn in H'. destruct H' as [-> |  H']. {left. easy. }
          right. rewrite <- PeanoNat.Nat.succ_lt_mono. easy.
    Qed.

    Definition open_rec_lc_lam : forall s t n, lc' 0 s -> lc'_lam (S n) t -> lc' n (open_rec n s t).
    Proof.
    intros s t n H1 H2.
    inversion H2.
    - subst. unfold app_. rewrite retract_open_rec.
      simpl. apply retract_lc.
      constructor; apply open_rec_lc; try easy.
    - unfold ab_. rewrite retract_open_rec.
      simpl. apply retract_lc. constructor.
      subst. apply open_rec_lc; try easy.
    - subst. unfold bvar_. rewrite retract_open_rec. simpl.
      destruct (nat_shenenigans k n). { easy. }
      + subst. rewrite PeanoNat.Nat.eqb_refl. 
        apply lc_weaken with (n := 0). lia. easy.
      + destruct (Nat.eqb n k) eqn:n_eq_k.
        { apply lc_weaken with (n:=0). lia. easy. }
        apply retract_lc. constructor. easy.
    Defined.    

    Variable value : exp -> Prop.

    Inductive value_lam : exp -> Prop := 
        | value_ab (t : exp) : lc' 0 (ab_ t) -> value_lam (ab_ t)
        | value_bvar (n : nat) : value_lam (bvar_ n)
    .

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.
    

    Inductive step_lam : Ctx -> exp -> Ctx -> exp -> Prop :=
        | stepBeta   ctx s         t : value t -> step_lam ctx (app_ (ab_ s) t) ctx (open_rec 0 t s)
        | stepAppL   ctx s ctx' s' t : value t -> step ctx s ctx' s' -> step_lam ctx (app_ s t) ctx' (app_ s' t)
        | stepAppR s ctx t ctx' t'   : step ctx t ctx' t' -> step_lam ctx (app_ s t) ctx' (app_ s t')
    .

    Lemma lc_ab_inv : forall s n, lc' n (ab_ s) -> lc' (S n) s.
    intros s n Hlc.
    apply retract_lc_rev in Hlc. inversion Hlc; subst; try (apply retract_inj in H0; easy).
    apply retract_inj in H0. inversion H0. subst. easy.
    Qed.


    Definition preservation_lam : forall c e c' e', lc' 0 e -> step_lam c e c' e' -> lc' 0 e'.
    Proof.
        intros c e c' e' lc_e.
        induction 1.
        - apply retract_lc_rev in lc_e. inversion lc_e; try (apply retract_inj in H1; easy).
          apply retract_inj in H1. inversion H1. subst.
          apply open_rec_lc; try easy.
          apply lc_ab_inv. easy.
        - apply retract_lc_rev in lc_e. inversion lc_e; try (apply retract_inj in H2; easy).
          apply retract_inj in H2. inversion H2; subst; try (apply retract_inj in H2; easy).
          apply retract_lc. constructor; try easy. apply (preservation ctx s ctx' s'); easy.
        - apply retract_lc_rev in lc_e. inversion lc_e; try (apply retract_inj in H1; easy).
          subst. apply retract_inj in H1. inversion H1. subst.
          apply retract_lc. constructor. {easy. } 
          apply (preservation ctx t ctx' t'); easy.      
    Defined.
    
End exp_lam.