From Imp Require Export header_extensible.

Section exp_ite.
    Variable exp : Type.

    Inductive exp_ite : Type := 
        | bool_lit : bool -> exp_ite
        | ite : exp -> exp -> exp -> exp_ite
    .

    Context `{retract exp_ite exp}.

    Definition ite_  (s0 s1 s2 : exp  ) : _ := inj (ite s0 s1 s2).
    Definition bool_lit_  (b : bool) : _ := inj (bool_lit b).

    Variable open_rec : nat -> exp -> exp -> exp.

    Definition open_rec_ite (k : nat) (s : exp) (t : exp_ite) : exp := 
        match t with 
            | bool_lit b => bool_lit_ b
            | ite c t f => ite_ (open_rec k s c) (open_rec k s t) (open_rec k s f)
        end.

    Variable retract_open_rec : forall (n : nat) s (e : exp_ite),
          open_rec n s (inj e) = open_rec_ite n s e.

    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc :forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.
    
    Inductive lc'_ite : nat -> exp -> Prop := 
        | lc_ite  n c t f : lc' n c -> lc' n t -> lc' n f -> lc'_ite n (ite_ c t f)
        | lc_bool_lit   n b    : lc'_ite n (bool_lit_ b)
    .
    Variable retract_lc: forall n e, lc'_ite n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_ite n (inj e).

    Definition lc_weaken_ite : forall s n m, n <= m -> lc'_ite n s -> lc' m s.
    Proof.
      intros s n m n_le_m H'. 
      apply retract_lc.
      induction H'.
      - constructor; apply lc_weaken with (n := n); easy.
      - constructor. 
    Defined.

    Definition open_rec_lc_ite : forall s t n, lc' 0 s -> lc'_ite (S n) t -> lc' n (open_rec n s t).
    Proof.
        intros s t n H1 H2.
        inversion H2; subst.
        - unfold ite_. rewrite retract_open_rec.
          simpl. apply retract_lc. constructor; apply open_rec_lc; try easy.
        - unfold bool_lit_. rewrite retract_open_rec.
          simpl. apply retract_lc. constructor; apply open_rec_lc; try easy.
    Defined.

    Variable value : exp -> Prop.

    Inductive value_ite : exp -> Prop := 
        | value_true : value_ite (bool_lit_ true)
        | value_false : value_ite (bool_lit_ false)
    .

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.
    

    Inductive step_ite : Ctx -> exp -> Ctx -> exp -> Prop :=
        | stepIteL   ctx           t  f : step_ite ctx (ite_ (bool_lit_ true) t f)  ctx t
        | stepIteR   ctx           t  f : step_ite ctx (ite_ (bool_lit_ false) t f) ctx f
        | stepIte    ctx s ctx' s' t  f : step ctx s ctx' s' -> step_ite ctx (ite_ s t f) ctx' (ite_ s' t f)
    .

    
    Definition preservation_ite : forall c e c' e', lc' 0 e -> step_ite c e c' e' -> lc' 0 e'.
    Proof. 
        intros c e c' e' lc_e.
        induction 1.
        - unfold ite_ in lc_e. apply retract_lc_rev in lc_e.
          inversion lc_e. 
            + unfold ite_ in *. apply retract_inj in H0. inversion H0. subst. easy.
            + unfold bool_lit_ in *. apply retract_inj in H2. easy.
        - unfold ite_ in lc_e. apply retract_lc_rev in lc_e.
          inversion lc_e. 
            + unfold ite_ in *. apply retract_inj in H0. inversion H0. subst. easy.
            + unfold bool_lit_ in *. apply retract_inj in H2. easy.
        - apply retract_lc_rev in lc_e.
          apply retract_lc.
          inversion lc_e. 
          + apply retract_inj in H1. inversion H1. subst.
            apply lc_ite; try assumption.
            apply preservation in H0; easy.
          + apply retract_inj in H3. easy.
    Defined.
        
End exp_ite.