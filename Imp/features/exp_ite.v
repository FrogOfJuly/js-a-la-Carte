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

    Definition open_rec_ite (k : nat) (u : exp) (e : exp_ite) : exp := 
        match e with 
            | bool_lit b => bool_lit_ b
            | ite c t f => ite_ (open_rec k u c) (open_rec k u t) (open_rec k u f)
        end.

    Variable lc' : nat -> exp -> Prop.

    Inductive lc'_ite : nat -> exp -> Prop := 
        | lc_ite  n c t f : lc' n c -> lc' n t -> lc' n f -> lc'_ite n (ite_ c t f)
        | lc_bool_lit   n b    : lc'_ite n (bool_lit_ b)
    .

    Variable value : exp -> Prop.

    Inductive value_ite : exp -> Prop := 
        | value_true : value_ite (bool_lit_ true)
        | value_false : value_ite (bool_lit_ false)
    .

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    

    Inductive step_ite : Ctx -> exp -> Ctx -> exp -> Prop :=
        | stepIteL   ctx           t  f : step_ite ctx (ite_ (bool_lit_ true) t f)  ctx t
        | stepIteR   ctx           t  f : step_ite ctx (ite_ (bool_lit_ false) t f) ctx f
        | stepIte    ctx s ctx' s' t  f : step ctx s ctx' s' -> step_ite ctx (ite_ s t f) ctx' (ite_ s' t f)
    .

    Lemma preservation_ite : forall c e c' e', lc' 0 e -> step_ite c e c' e' -> lc' 0 e'.
    Proof. 
        intros c e c' e' cl_e.
        induction 1; admit.
    Admitted.
        
End exp_ite.

