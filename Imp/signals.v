From Imp Require Import header_extensible exp_ite exp_lam.

Inductive exp : Type := 
    | In_exp_lam : exp_lam exp -> exp
    | In_exp_ite : exp_ite exp -> exp
.


#[refine] Global Instance retract_exp_exp_lam : retract (exp_lam exp) exp := { 
    retract_I := In_exp_lam; 
    retract_R := fun x => match x with In_exp_lam t => Some t | _ => None end 
    }.
Proof.
    - intros x. reflexivity.
    - intros x y H. destruct y. 
      all: try discriminate.
      inversion H. subst. reflexivity.
Qed.

#[refine] Global Instance retract_exp_exp_ite : retract (exp_ite exp) exp := { 
    retract_I := In_exp_ite; 
    retract_R := fun x => match x with In_exp_ite t => Some t | _ => None end 
    }.
Proof.
    - intros x. reflexivity.
    - intros x y H. destruct y. 
      all: try discriminate.
      inversion H. subst. reflexivity.
Qed.
    
Fixpoint open_rec (k : nat) (u : exp) (e : exp) : exp := 
    match e with 
        | In_exp_lam e => open_rec_lam _ open_rec k u e
        | In_exp_ite e => open_rec_ite _ open_rec k u e
    end
.



Inductive lc' : nat -> exp -> Prop := 
    | lc_in_lam n e : lc'_lam _ lc' n e -> lc' n e
    | lc_in_ite n e : lc'_ite _ lc' n e -> lc' n e
.


Inductive value : exp -> Prop := 
    | value_in_lam (e : exp) : value_lam _ lc' e -> value e
    | value_in_ite (e : exp) : value_ite _ e -> value e
.

From Imp Require Import context.

Module SIGNALS (Import Atom : ATOM) (Import String : STRING).

Module Import Env := Imp.context.Env (Atom) (String).

Inductive stored_val : Type := val_with_proof : forall (v : exp), value v -> stored_val.

Record Ctx := mkCtx {
    store : Env.AtomEnv.t stored_val;
    (* 
        signalStore; 
        hiddenGlobalState;
        componentStore?
    *)
}.

Inductive step : Ctx -> exp -> Ctx -> exp -> Prop := 
    | step_in_lam (c : Ctx) s c' s' : step_lam _ open_rec value _ step c s c' s' -> step c s c' s'
    | step_in_ite (c : Ctx) s c' s' : step_ite _ _ step c s c' s' -> step c s c' s'
.

Definition lc := lc' 0.
Definition open := open_rec 0.

Definition Progress := forall c e, 
  lc e -> 
  value e \/ (exists e' c', step c e c' e').

Definition Preservation := forall c e c' e', 
  lc e -> 
  step c e c' e' -> 
  lc e'.

Lemma preservation : Preservation.
Proof. 
    intros c e c' e'.
    unfold lc in *.
    induction 2.
    - apply (preservation_lam _ open_rec lc' value _ step c s c' s'); easy.
    - apply (preservation_ite _ open_rec lc' value _ step c s c' s'); easy.
Qed.

End SIGNALS.


