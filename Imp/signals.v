From Imp Require Import header_extensible exp_ite exp_lam exp_mut exp_err.

Inductive exp : Type := 
    | In_exp_lam : exp_lam exp -> exp
    | In_exp_ite : exp_ite exp -> exp
    | In_exp_mut : exp_mut exp -> exp
    | In_exp_err : exp_err exp -> exp
.


#[refine] Global Instance retract_exp_exp_lam : retract (exp_lam exp) exp := { 
    retract_I := In_exp_lam; 
    retract_R := fun x => match x with In_exp_lam t => Some t | _ => None end 
    }.
Proof.
    - intros x. easy.
    - intros x y H. destruct y; (try easy).
      inversion H. easy.
Defined.

#[refine] Global Instance retract_exp_exp_ite : retract (exp_ite exp) exp := { 
    retract_I := In_exp_ite; 
    retract_R := fun x => match x with In_exp_ite t => Some t | _ => None end 
    }.
Proof.
    - intros x. easy.
    - intros x y H. destruct y; (try easy).
      inversion H. easy.
Defined.

#[refine] Global Instance retract_exp_exp_mut : retract (exp_mut exp) exp := { 
    retract_I := In_exp_mut; 
    retract_R := fun x => match x with In_exp_mut t => Some t | _ => None end 
    }.
Proof.
    - intros x. easy.
    - intros x y H. destruct y; (try easy).
      inversion H. easy.
Defined.

#[refine] Global Instance retract_exp_exp_err : retract (exp_err exp) exp := { 
    retract_I := In_exp_err; 
    retract_R := fun x => match x with In_exp_err t => Some t | _ => None end 
    }.
Proof.
    - intros x. easy.
    - intros x y H. destruct y; (try easy).
      inversion H. easy.
Defined.
    
Fixpoint open_rec (k : nat) (u : exp) (e : exp) : exp := 
    match e with 
        | In_exp_lam e => open_rec_lam _ open_rec k u e
        | In_exp_ite e => open_rec_ite _ open_rec k u e
        | In_exp_mut e => open_rec_mut _ open_rec k u e
        | In_exp_err e => open_rec_err _ open_rec k u e
    end
.



Inductive lc' : nat -> exp -> Prop := 
    | lc_in_lam n e : lc'_lam _ lc' n e -> lc' n e
    | lc_in_ite n e : lc'_ite _ lc' n e -> lc' n e
    | lc_in_mut n e : lc'_mut _ lc' n e -> lc' n e
    | lc_in_err n e : lc'_err _ lc' n e -> lc' n e
.


Inductive value : exp -> Prop := 
    | value_in_lam (e : exp) : value_lam _ lc' e -> value e
    | value_in_ite (e : exp) : value_ite _ e -> value e
    | value_in_mut (e : exp) : value_mut _ e -> value e
    | value_in_err (e : exp) : value_err _ e -> value e
.


Definition retract_lc_rev_ite : forall (n : nat) (e : exp_ite exp),
            lc' n (inj e) -> lc'_ite exp lc' n (inj e).
Proof.
    intros n e.
    inversion 1; easy.
Qed.

Definition retract_lc_rev_lam : forall (n : nat) (e : exp_lam exp),
        lc' n (inj e) -> lc'_lam exp lc' n (inj e).
Proof.
    intros n e.
    inversion 1; easy.
Qed.

Definition retract_lc_rev_mut : forall (n : nat) (e : exp_mut exp),
        lc' n (inj e) -> lc'_mut exp lc' n (inj e).
Proof.
    intros n e.
    inversion 1; easy.
Qed.

Definition retract_lc_rev_err : forall (n : nat) (e : exp_err exp),
        lc' n (inj e) -> lc'_err exp lc' n (inj e).
Proof.
    intros n e.
    inversion 1; easy.
Qed.

Definition retract_open_rec_rev_lam : forall (n : nat) s (e : exp_lam exp),
            open_rec n s (inj e) = open_rec_lam _ open_rec n s e.
Proof.
    intros n s e. easy.
Qed.

Definition retract_open_rec_rev_ite : forall (n : nat) s (e : exp_ite exp),
            open_rec n s (inj e) = open_rec_ite _ open_rec n s e.
Proof.
    intros n s e. easy.
Qed.

Definition retract_open_rec_rev_mut : forall (n : nat) s (e : exp_mut exp),
            open_rec n s (inj e) = open_rec_mut _ open_rec n s e.
Proof.
    intros n s e. easy.
Qed.

Definition retract_open_rec_rev_err : forall (n : nat) s (e : exp_err exp),
            open_rec n s (inj e) = open_rec_err _ open_rec n s e.
Proof.
    intros n s e. easy.
Qed.

Fixpoint lc_weaken   : forall s n m, n <= m -> lc' n s -> lc' m s.
intros s n m n_le_m Hlc.
inversion Hlc; subst.
- apply (lc_weaken_lam exp _ lc_weaken lc_in_lam _) with (n := n); easy.
- apply (lc_weaken_ite exp _ lc_weaken lc_in_ite _) with (n := n); easy.
- apply (lc_weaken_mut exp _ lc_weaken lc_in_mut _) with (n := n); easy.
- apply (lc_weaken_err exp _ lc_weaken lc_in_err _) with (n := n); easy.
Qed.

Fixpoint open_rec_lc : forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
Proof.
intros s t n H1 H2.
inversion H2; subst.
- apply (open_rec_lc_lam exp open_rec retract_open_rec_rev_lam lc' open_rec_lc lc_weaken lc_in_lam); easy.
- apply (open_rec_lc_ite exp open_rec retract_open_rec_rev_ite lc' open_rec_lc lc_in_ite); easy.
- apply (open_rec_lc_mut exp open_rec retract_open_rec_rev_mut lc' open_rec_lc lc_in_mut); easy.
- apply (open_rec_lc_err exp open_rec retract_open_rec_rev_err lc' open_rec_lc lc_in_err); easy.
Qed.

Fixpoint value_lc : forall v, value v -> lc' 0 v.
Proof.
    intros v. induction 1.
    - apply (value_lc_lam _ _); easy.
    - apply (value_lc_ite _ _ lc_in_ite); easy.
    - apply (value_lc_mut _ _ lc_in_mut); easy.
    - apply (value_lc_err _ _); easy.
Qed.

From Imp Require Import context.

Definition VarEnv := Env (sig value).

Record Ctx := mkCtx {
        store : VarEnv;
}.

#[refine] Global Instance ctx_supports_store : hasProj Ctx VarEnv := {
    get_proj := store;
    set_proj := (fun x c => mkCtx x);
}.
Proof.
    - intros. easy.
    - intros. destruct c. simpl. easy.
Defined.

Inductive step : Ctx -> exp -> Ctx -> exp -> Prop := 
    | step_in_lam (c : Ctx) s c' s' : step_lam _ open_rec value _ step c s c' s' -> step c s c' s'
    | step_in_ite (c : Ctx) s c' s' : step_ite _ _                step c s c' s' -> step c s c' s'
    | step_in_mut (c : Ctx) s c' s' : step_mut _ _ _              step c s c' s' -> step c s c' s'
    | step_in_err (c : Ctx) s c' s' : step_err _ _                step c s c' s' -> step c s c' s'
.

Definition lc := lc' 0.
Definition open := open_rec 0.

Fixpoint preservation : forall c e c' e', 
    lc e -> 
    step c e c' e' -> 
    lc e'. 
Proof. 
    intros c e c' e'.
    unfold lc in *.
    induction 2.
    - apply (preservation_lam exp open_rec lc' open_rec_lc lc_in_lam retract_lc_rev_lam value Ctx step preservation c s c' s'); easy.
    - apply (preservation_ite exp lc' lc_in_ite retract_lc_rev_ite Ctx step preservation c s c' s'); easy.
    - apply (preservation_mut exp lc' lc_in_mut retract_lc_rev_mut value value_lc Ctx step preservation c s c' s'); easy.
    - apply (preservation_err exp lc' lc_in_err retract_lc_rev_err Ctx step preservation c s c' s'); easy.
Defined.

