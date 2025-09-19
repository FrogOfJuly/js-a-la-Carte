From Imp Require Export header_extensible.

Section exp_mut.
    Variable exp : Type.

    Inductive exp_mut : Type := 
        | exp_loc : nat -> exp_mut
        | exp_set : exp -> exp -> exp_mut
        | exp_deref : exp -> exp_mut
        | exp_ref : exp -> exp_mut
    .

    Context `{Hretr : retract exp_mut exp}.

    Definition exp_loc_ (n : nat) : _ := inj (exp_loc n).
    Definition exp_set_ (e1 e2 : exp) : _ := inj (exp_set e1 e2).
    Definition exp_deref_ (e : exp) : _ := inj (exp_deref e).
    Definition exp_ref_ (e : exp) : _ := inj (exp_ref e).

    Variable open_rec : nat -> exp -> exp -> exp.

    Definition open_rec_mut (k : nat) (s : exp) (t : exp_mut) : exp := 
        match t with 
            | exp_loc n => inj (exp_loc n)
            | exp_set v x => inj (exp_set (open_rec k s x) (open_rec k s v))
            | exp_deref x => inj (exp_deref (open_rec k s x))
            | exp_ref x => inj (exp_ref (open_rec k s x))
        end
    .

    Variable retract_open_rec : forall (n : nat) s (e : exp_mut),
          open_rec n s (inj e) = open_rec_mut n s e.

    
    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc :forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.


    Inductive lc'_mut : nat -> exp -> Prop := 
        | lc_loc n l: lc'_mut n (exp_loc_ l)
        | lc_set n v x : lc' n v -> lc' n x -> lc'_mut n (exp_set_ v x)
        | lc_deref n x : lc' n x -> lc'_mut n (exp_deref_ x)
        | lc_ref n x : lc' n x -> lc'_mut n (exp_ref_ x)
    .

    Variable retract_lc: forall n e, lc'_mut n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_mut n (inj e).

    Definition lc_weaken_mut : forall s n m, n <= m -> lc'_mut n s -> lc' m s.
    Proof. Admitted.

    Definition open_rec_lc_mut : forall s t n, lc' 0 s -> lc'_mut (S n) t -> lc' n (open_rec n s t).
    Proof. Admitted.

    Variable value : exp -> Prop.

    Inductive value_mut : exp -> Prop := 
    .

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.


    Inductive step_mut : Ctx -> exp -> Ctx -> exp -> Prop :=
    .

    Definition preservation_mut : forall c e c' e', lc' 0 e -> step_mut c e c' e' -> lc' 0 e'.
    Proof. Admitted.

End exp_mut.