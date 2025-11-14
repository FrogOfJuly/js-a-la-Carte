From Imp Require Import exp_err exp_mut.

Section int_exp_mut.
    Variable exp : Type.
    Context `{Herr : retract (exp_err exp) exp}.
    Context `{Hmut : retract (exp_mut exp) exp}.

    Variable open_rec : nat -> exp -> exp -> exp.

    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc :forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.

    Variable retract_lc_mut: forall n e, (lc'_mut _ lc' n e) -> lc' n e.
    Variable retract_lc_err: forall n e, (lc'_err _ lc' n e) -> lc' n e.
    Variable retract_lc_rev_mut: forall n (e : exp_mut exp), lc' n (inj e) -> lc'_mut _ lc' n (inj e).
    Variable retract_lc_rev_err: forall n (e : exp_err exp), lc' n (inj e) -> lc'_err _ lc' n (inj e).

    Variable value : exp -> Prop.
    Variable value_lc : forall v, value v -> lc' 0 v.


    Variable tag : Type.
    Variable tag_of : exp -> tag -> Prop.
    Variable tag_of_decidable: forall e t, ~tag_of e t \/ tag_of e t.

    Context `{Herr_tag : retract tag_err tag}.
    Context `{Hmut_tag : retract tag_mut tag}.

    Variable Ctx : Type.
    Context `{hasProj Ctx (Env (sig value))}.

    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.

    Inductive step_int_mut_err : Ctx -> exp -> Ctx -> exp -> Prop := 
        | step_bad_setref c l v (vp : value v):
            Env.mem l (get_proj c) = false ->
            step_int_mut_err c (exp_setref_ _ (exp_loc_ _ l) v) c (err_ _ (exp_loc_ _ l))
        | step_bad_deref c l: 
            Env.find l (get_proj c) = None -> 
            step_int_mut_err c (exp_deref_ _ (exp_loc_ _ l)) c (err_ _ (exp_loc_ _ l))
        (* Bad reduction propagation *)
        | step_setref_red l c s c' s': 
            step c s c' (err_ _ s') -> 
            step_int_mut_err c (exp_setref_ _ (exp_loc_ _ l) s) c' (err_ _ s')
        | step_ref_red c s c' s': 
            step c s c' (err_ _ s') -> 
            step_int_mut_err c (exp_ref_ _ s) c' (err_ _ s')
        (* Bad labels *)
        | step_bad_label_setref c e v: 
            ~ tag_of e (tag_loc_ _) ->
            step_int_mut_err c (exp_setref_ _ e v) c (err_ _ e)
        | step_bad_label_deref c e : 
            ~ tag_of e (tag_loc_ _) ->
            step_int_mut_err c (exp_deref_ _ e) c (err_ _ e)
        . 

    Definition preservation_mut_err : forall c e c' e', lc' 0 e -> step_int_mut_err c e c' e' -> lc' 0 e'.
    Proof. 
        intros c e c' e' lc_e.
        induction 1. 
        - apply retract_lc_err. constructor.
          apply retract_lc_mut. constructor.
        - apply retract_lc_err. constructor.
          apply retract_lc_mut. constructor.
        - apply preservation in H0; try easy.
          remember (exp_setref exp (exp_loc_ exp l) s) as e.
          apply retract_lc_rev_mut in lc_e.
          inversion lc_e.
          + subst. apply retract_inj in H3.
            inversion H3.
          + apply retract_inj in H1.
            subst e. inversion H1.
            subst. easy.
          + subst. apply retract_inj in H1.
            inversion H1.
          + subst. apply retract_inj in H1.
            inversion H1.
        - apply preservation in H0; try easy.
          apply retract_lc_rev_mut in lc_e.
          remember (exp_ref exp s) as e.
          inversion lc_e.
          + subst. apply retract_inj in H3.
            inversion H3.
          + subst. apply retract_inj in H1.
            inversion H1.
          + subst. apply retract_inj in H1.
            inversion H1.
          + subst. apply retract_inj in H1.
            inversion H1. subst. easy.
        - apply retract_lc_rev_mut in lc_e.
          remember (exp_setref exp e v) as e'.
          inversion lc_e.
          + subst. apply retract_inj in H3.
            inversion H3.
          + subst. apply retract_inj in H1.
            inversion H1. subst.
            apply retract_lc_err. constructor. easy.
          + subst. apply retract_inj in H1.
            inversion H1.
          + subst. apply retract_inj in H1.
            inversion H1. 
        - apply retract_lc_rev_mut in lc_e.
          remember (exp_deref exp e) as e'.
          inversion lc_e.
          + subst. apply retract_inj in H3.
            inversion H3.
          + subst. apply retract_inj in H1.
            inversion H1.
          + subst. apply retract_inj in H1.
            inversion H1. subst.
            apply retract_lc_err. constructor. easy.
          + subst. apply retract_inj in H1.
            inversion H1. 
    Defined.
            

          
          
          
    
End int_exp_mut.