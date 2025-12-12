From Imp Require Export header_extensible.
From Imp Require Export elpi_shenanigans.

From Stdlib Require Import Lia.

From Imp Require Export elpi_shenanigans.

Section exp_lam.

    Variable exp : Type.

    #[represents = exp]
    Elpi RegisterVariable (exp).
    
    (* #[extends = exp, db = exp_lam]
    Elpi RegisterExtensionInline *)
    Inductive exp_lam : Type := 
        | ab : exp -> exp_lam
        | app : exp -> exp -> exp_lam
        | bvar : nat -> exp_lam
    .

    Elpi SetSectionDeps (exp_lam).

    Context `{Hretr : retract exp_lam exp}.

    #[represents = retract_exp_exp_lam]
    Elpi RegisterVariable (Hretr).

    Definition ab_  (s0 : exp  ) : _ := inj (ab s0).
    Definition app_  (s0 s1 : exp  ) : _ := inj (app s0 s1).
    Definition bvar_  (n : nat) : _ := inj (bvar n).

    Elpi SetSectionDeps (ab_).
    Elpi SetSectionDeps (app_).
    Elpi SetSectionDeps (bvar_).

    
    Variable open_rec : nat -> exp -> exp -> exp.

    #[represents = open_rec]
    Elpi RegisterVariable (open_rec).

    Definition open_rec_lam (k : nat) (u : exp) (e : exp_lam) : exp := 
        match e with 
            | bvar n => if Nat.eqb k n then u else bvar_ n
            | app t t'   => app_ (open_rec k u t) (open_rec k u t')
            | ab t       => ab_ (open_rec (S k) u t)
        end.

    Elpi SetSectionDeps (open_rec_lam).

    Variable retract_open_rec : forall (n : nat) s (e : exp_lam),
            open_rec n s (inj e) = open_rec_lam n s e.

    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc : forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.

    #[represents = retract_open_rec_rev_lam]
    Elpi RegisterVariable (retract_open_rec).

    #[represents = lc']
    Elpi RegisterVariable (lc').

    #[represents = open_rec_lc]
    Elpi RegisterVariable (open_rec_lc).

    #[represents = lc_weaken]
    Elpi RegisterVariable (lc_weaken).

    
    Inductive lc'_lam : nat -> exp -> Prop := 
        | lc_app  n t t' : lc' n t -> lc' n t' -> lc'_lam n (app_ t t')
        | lc_ab   n t    : lc' (S n) t  -> lc'_lam n (ab_ t)
        | lc_bvar k n    : k < n -> lc'_lam n (bvar_ k)
    .

    Elpi SetSectionDeps (lc'_lam).

    Variable retract_lc: forall n e, lc'_lam n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_lam n (inj e).

    #[represents = retract_lc_lam]
    Elpi RegisterVariable (retract_lc).

    #[represents = retract_lc_rev_lam]
    Elpi RegisterVariable (retract_lc_rev).
    
    Lemma lc_ab_inv : forall s n, lc' n (ab_ s) -> lc' (S n) s.
      intros s n Hlc.
      apply retract_lc_rev in Hlc. inversion Hlc; subst; try (apply retract_inj in H; easy).
      apply retract_inj in H. inversion H. subst. easy.
    Qed.

    Lemma nat_shenenigans : forall n m, n < S m -> n = m \/ n < m.
    Proof. 
      intros n. 
      induction n.
      - intros m. destruct m. {left. easy. } right. lia.
      - intros m H'. apply PeanoNat.lt_S_n in H'.
        destruct m. { lia. }
        apply IHn in H'. destruct H' as [-> |  H']. {left. easy. }
        right. lia.
    Qed.

    Definition lc_weaken_lam : forall s n m, n <= m -> lc'_lam n s -> lc' m s.
    Proof.
      intros s n m n_le_m H'. 
      apply retract_lc.
      induction H'.
      - constructor; apply lc_weaken with (n := n); easy.
      - constructor. apply lc_weaken with (n := S n). lia. easy.
      - constructor. lia.
    Defined.

    Elpi SetSectionDeps (lc_weaken_lam).

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

    Elpi SetSectionDeps (open_rec_lc_lam).

    (* #[extends = open_rec_lc]
    Elpi RegisterExtension (open_rec_lc_lam). *)
      
    Variable value : exp -> Prop.
    Variable value_lc : forall v, value v -> lc' 0 v.


    #[represents = value]
    Elpi RegisterVariable (value).

    #[represents = value_lc]
    Elpi RegisterVariable (value_lc).

    (* #[extends = value]
    Elpi RegisterExtensionInline *)
    Inductive value_lam : exp -> Prop := 
        | value_ab (t : exp) : lc' 0 (ab_ t) -> value_lam (ab_ t)
    .

    Elpi SetSectionDeps (value_lam).

    Definition value_lc_lam : forall v, value_lam v -> lc' 0 v.
    Proof.
        intros v. inversion 1. easy.
    Defined.

    Elpi SetSectionDeps (value_lc_lam).

    (* #[extends = value_lc]
    Elpi RegisterExtension (value_lc_lam). *)

    Variable tag : Type.

    #[represents = tag]
    Elpi RegisterVariable (tag).
    
    (* #[extends = tag]
    Elpi RegisterExtensionInline *)
    Inductive tag_lam := 
      | tag_ab  : tag_lam
      | tag_var : tag_lam
    .

    Elpi SetSectionDeps (tag_lam).

    Context `{Htag : retract tag_lam tag}.

    #[represents = retract_tag_tag_lam]
    Elpi RegisterVariable (Htag).

    Definition tag_ab_ := inj tag_ab.
    Definition tag_var_ := inj tag_var.

    Elpi SetSectionDeps (tag_ab_).
    Elpi SetSectionDeps (tag_var_).

    Inductive tag_of_lam : exp -> tag -> Prop :=
      | tag_of_abs e : tag_of_lam (ab_ e) tag_ab_
      | tag_of_var n : tag_of_lam (bvar_ n) tag_var_
    .

    Elpi SetSectionDeps (tag_of_lam).
    

    Lemma tag_of_decidable_lam : forall (e : exp_lam) (t : tag_lam), ~tag_of_lam (inj e) (inj t) \/ tag_of_lam (inj e) (inj t).
    Proof.
      intros. destruct e; destruct t;
      try (right; constructor).
      all: left; inversion 1.
      all: try apply retract_inj in H1.
      all: try apply retract_inj in H2.
      all: easy.
    Defined.

    Elpi SetSectionDeps (tag_of_decidable_lam).

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.

    #[represents = Ctx]
    Elpi RegisterVariable (Ctx).

    #[represents = step]
    Elpi RegisterVariable (step).

    #[represents = preservation]
    Elpi RegisterVariable (preservation).
    

    (* #[extends = step]
    Elpi RegisterExtensionInline *)
    Inductive step_lam : Ctx -> exp -> Ctx -> exp -> Prop :=
        | stepBeta   ctx s         t : value t -> step_lam ctx (app_ (ab_ s) t) ctx (open_rec 0 t s)
        | stepAppL   ctx s ctx' s' t : value t -> step ctx s ctx' s' -> step_lam ctx (app_ s t) ctx' (app_ s' t)
        | stepAppR s ctx t ctx' t'   : step ctx t ctx' t' -> step_lam ctx (app_ s t) ctx' (app_ s t')
    .

    Elpi SetSectionDeps (step_lam).


    Definition preservation_lam : forall c e c' e', lc' 0 e -> step_lam c e c' e' -> lc' 0 e'.
    Proof.
        intros c e c' e' lc_e.
        induction 1.
        - apply retract_lc_rev in lc_e. inversion lc_e; try (apply retract_inj in H0; easy).
          apply retract_inj in H0. inversion H0. subst.
          apply open_rec_lc; try easy.
          apply lc_ab_inv. easy.
        - apply retract_lc_rev in lc_e. inversion lc_e; try (apply retract_inj in H1; easy).
          apply retract_inj in H1. inversion H1; subst; try (apply retract_inj in H1; easy).
          apply retract_lc. constructor; try easy. apply (preservation ctx s ctx' s'); easy.
        - apply retract_lc_rev in lc_e. inversion lc_e; try (apply retract_inj in H0; easy).
          subst. apply retract_inj in H0. inversion H0. subst.
          apply retract_lc. constructor. {easy. } 
          apply (preservation ctx t ctx' t'); easy.      
    Defined.

    Elpi SetSectionDeps (preservation_lam).
    
End exp_lam.