From Imp Require Export header_extensible.

Section exp_err.
    Variable exp : Type.

    Inductive exp_err : Type := 
        | err (e : exp) : exp_err
    .

    Context `{Herr : retract exp_err exp}.

    Definition err_  (e : exp) : _ := inj (err e).

    Variable open_rec : nat -> exp -> exp -> exp.

    Definition open_rec_err (k : nat) (s : exp) (t : exp_err) : exp := 
        match t with 
            | err e => err_ (open_rec k s e)
        end.
    
    Variable retract_open_rec : forall (n : nat) s (e : exp_err),
          open_rec n s (inj e) = open_rec_err n s e.

    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc :forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.
    
    Inductive lc'_err : nat -> exp -> Prop := 
        | lc_err n e : lc' n e -> lc'_err n (err_ e)
    .

    Variable retract_lc: forall n e, lc'_err n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_err n (inj e).

    Definition lc_weaken_err : forall s n m, n <= m -> lc'_err n s -> lc' m s.
    Proof.
        intros s n m n_le_m.
        induction 1. apply retract_lc. constructor. 
        apply lc_weaken with (n := n); easy.
    Defined.

    Definition open_rec_lc_err : forall s t n, lc' 0 s -> lc'_err (S n) t -> lc' n (open_rec n s t).
    Proof.
        intros s t n lc_s lc_err.
        inversion lc_err. subst. unfold err_. rewrite retract_open_rec.
        simpl. apply retract_lc. constructor.
        apply open_rec_lc; try easy.
    Defined.
    
    Variable value : exp -> Prop.
    Variable value_lc : forall v, value v -> lc' 0 v.

    Inductive value_err : exp -> Prop := 
    .

    Definition value_lc_err : forall v, value_err v -> lc' 0 v.
    Proof.
        intros v. induction 1.
    Defined.

    Variable tag : Type.
    
    Inductive tag_err := 
    .

    Context `{Htag : retract tag_err tag}.

    Inductive tag_of_err : exp -> tag -> Prop :=
    .

    Lemma tag_of_decidable_err : forall (e : exp_err) (t : tag_err), ~tag_of_err (inj e) (inj t) \/ tag_of_err (inj e) (inj t).
    Proof.
      intros. destruct e; destruct t;
      left; inversion 1.
    Defined.

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.
    

    Inductive step_err : Ctx -> exp -> Ctx -> exp -> Prop :=
        | step_err_red c e c' e' : step c e c' e' -> step_err c (err_ e) c' (err_ e')
    .

    
    Definition preservation_err : forall c e c' e', lc' 0 e -> step_err c e c' e' -> lc' 0 e'.
    Proof. 
        intros c e c' e' lc_e.
        induction 1.
        apply retract_lc_rev in lc_e.
        inversion lc_e. subst.
        apply retract_inj in H0. inversion H0. subst.
        apply retract_lc. constructor.
        apply (preservation c e c' e'); easy.
    Defined.
        
End exp_err.