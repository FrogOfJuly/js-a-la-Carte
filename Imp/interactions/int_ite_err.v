From Imp Require Import exp_err exp_ite.

Section int_exp_ite.
    Variable exp : Type.
    Context `{Herr : retract (exp_err exp) exp}.
    Context `{Hite : retract (exp_ite exp) exp}.

    Variable open_rec : nat -> exp -> exp -> exp.

    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc :forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.

    Variable retract_lc_ite: forall n e, (lc'_ite _ lc' n e) -> lc' n e.
    Variable retract_lc_err: forall n e, (lc'_err _ lc' n e) -> lc' n e.
    Variable retract_lc_rev_ite: forall n (e : exp_ite exp), lc' n (inj e) -> lc'_ite _ lc' n (inj e).
    Variable retract_lc_rev_err: forall n (e : exp_err exp), lc' n (inj e) -> lc'_err _ lc' n (inj e).

    Variable value : exp -> Prop.
    Variable value_lc : forall v, value v -> lc' 0 v.


    Variable tag : Type.
    Variable tag_of : exp -> tag -> Prop.
    Variable tag_of_decidable: forall e t, ~tag_of e t \/ tag_of e t.

    Context `{Herr_tag : retract tag_err tag}.
    Context `{Hite_tag : retract tag_ite tag}.

    Variable Ctx : Type.
    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.

    Inductive step_int_ite_err : Ctx -> exp -> Ctx -> exp -> Prop := 
        | step_bad_cnd t f c e c' e': 
            step c e c' (err_ _ e') -> 
            step_int_ite_err c (ite_ _ e t f) c' (err_ _ e')
        | step_bad_beta e t f c: 
            value e  -> 
            ~ tag_of e (tag_bool_ _) -> 
            step_int_ite_err c (ite_ _ e t f) c (err_ _ e)
        . 

    Definition preservation_ite_err : forall c e c' e', lc' 0 e -> step_int_ite_err c e c' e' -> lc' 0 e'.
    Proof. 
        intros c e c' e' lc_e.
        induction 1. 
        - apply retract_lc_err. constructor. apply preservation in H.
            + apply retract_lc_rev_err in H. inversion H. 
              apply retract_inj in H0. inversion H0. subst.
              easy.
            + apply retract_lc_rev_ite in lc_e. inversion lc_e. 
              apply retract_inj in H0. inversion H0. { subst. easy. }
              all: subst; apply retract_inj in H2; inversion H2.
        - apply retract_lc_err. constructor. 
          apply value_lc. easy. 
    Defined.
End int_exp_ite.