From Imp Require Export header_extensible.

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

    Variable lc' : nat -> exp -> Prop.

    Inductive lc'_lam : nat -> exp -> Prop := 
        | lc_app  n t t' : lc' n t -> lc' n t' -> lc'_lam n (app_ t t')
        | lc_ab   n t    : lc' (S n) t  -> lc'_lam n (ab_ t)
        | lc_bvar k n    : n < k -> lc'_lam n (bvar_ k)
    .

    Variable retract_lc: forall n e, lc'_lam n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_lam n (inj e).

    Variable value : exp -> Prop.

    Inductive value_lam : exp -> Prop := 
        | value_ab (t : exp) : lc' 0 (ab_ t) -> value_lam (ab_ t)
        | value_bvar (n : nat) : value_lam (bvar_ n)
    .

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.
    

    Inductive step_lam : Ctx -> exp -> Ctx -> exp -> Prop :=
        | stepBeta   ctx s         t : value t -> step_lam ctx (app_ (ab_ s) t) ctx (open_rec 0 s t)
        | stepAppL   ctx s ctx' s' t : value t -> step ctx s ctx' s' -> step_lam ctx (app_ s t) ctx' (app_ s' t)
        | stepAppR s ctx t ctx' t'   : step ctx t ctx' t' -> step_lam ctx (app_ s t) ctx' (app_ s t')
    .


    Lemma preservation_lam : forall c e c' e', lc' 0 e -> step_lam c e c' e' -> lc' 0 e'.
    Proof.
        intros c e c' e' lc_e.
        induction 1.
        - apply retract_lc_rev in lc_e. inversion lc_e.
            + apply retract_inj in H1. inversion H1. subst. clear H1.
              
              
          
        
    Admitted.
    
End exp_lam.

