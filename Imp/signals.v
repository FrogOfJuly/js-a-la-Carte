From Imp Require Import header_extensible.
From Imp Require Import elpi_shenanigans.

(* Feature functors *)
From Imp Require Import exp_ite exp_lam exp_mut exp_err.
(* Interaction functors *)
From Imp Require Import int_lam_err int_ite_err int_mut_err.

From elpi Require Import elpi.

Elpi Export specialize_from_section.  

(* 

Command Register :- 
  (@local! => coq.elpi.acc "work.db" (clause _ _ _ _))

coq.elpi.add_predicate
coq.elpi.predicate

create_tc_predicate.elpi

rules can be local: @local! => ...

#[proof="begin"], #[proof(begin_if=...)], main-iterp-proof


*)

(*
TODO:
1. Generate specialized versions of non-recursive terms.
2. Make tactic for generating specialized recursive terms in their closing definitions
    a. Mark one argument as "structurally" decreasing and supply it after induction?
3. Template section? It seems that variables in sections and language properties mirror each other. 
   It might be beneficial to have a common source of truth for both of them.

   Maybe it should be a map from names to types that is discharged to sections for proofs 

   Elpi TemplateSection feature_functor.
        Variable exp : Type.
        Context `{Hretr : retract ?exp_lam exp}.

        Elpi MarkInduction 1 (* ----v *)
        Variable open_rec : nat -> exp -> exp -> exp. 
        ...
        ...
        ...
        Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.


   Elpi End feature_functor.

   #[template=feature_functor]
   Elpi FollowTemplate
   Section exp_lam.
     (* all variables from feature_functor are defined and registered *)

   End exp_lam.

   #[template=feature_functor]
   Elpi RealizeTemplate.

   Should generate proof obligations for each variable and try to prove them by induction and auto?
   Maybe it should be a record? 
   
*)


(* 

Inductive exp = Elpi Fix (exp_ite |+| exp_mut |+| exp_err |+| exp_lam).


*)

Inductive exp : Type := 
    | In_exp_lam : (specialize_from_section exp_lam) -> exp
    | In_exp_ite : exp_ite exp -> exp
    | In_exp_mut : exp_mut exp -> exp
    | In_exp_err : exp_err exp -> exp
.

(* Probably is a good idea to do 
    1. typechecking for corresponding mark
    2. give warning if no such mark exists *)
#[represeted_as = exp]
Elpi RegisterRepresented (exp).


Elpi Tactic exact_constructor.
Elpi Accumulate lp:{{
    solve (goal _ _ Ty _ [trm ( global (indt IndTyGRef))] as G) GL :- 
        % locate constructors Constr of inductive type IndTyGRef
        coq.env.indt IndTyGRef _ _ _ _ Constr _,
        % find corresponding terms(ConstrTerms) by querying environment(env.global) for constructor symbols
        % by relating output `r` to `indc c`
        std.map Constr (c\ r\ coq.env.global (indc c) r) ConstrTerms,
        % find their types by typechecking found terms by coq.typecheck
        % saving them into ConstrTypes
        std.map ConstrTerms (kt\ r\ coq.typecheck kt r _) ConstrTypes,
        % relate constructors to their types them together to establish correspondence
        % by zipping them together
        std.zip ConstrTerms ConstrTypes TermTypes,
        % find term corresponding to goal type
        std.assert! (std.mem TermTypes (pr C Ty)) "can't solve with exact constructors",
        % use it
        refine C G GL.
    solve (goal _ _ _Ty _ Args as _G) _GL :- 
        coq.ltac.fail _ ("Can't derive that: " ^ {std.any->string Args}).
}}.



Ltac try_derive_retract := match goal with 
    | [|- retract ?X ?Y] => exact (@Build_retract X Y
                                    ltac:(elpi exact_constructor ltac_term:(Y))
                                    ltac:(intros x; destruct x; try (apply Some; assumption); exact None)
                                    ltac:(simpl; intros; trivial)
                                    ltac:(simpl; intros x y; destruct y; inversion 1; congruence)
                            )
end.



#[refine] Global Instance retract_exp_exp_lam : retract (exp_lam exp) exp := ltac:(try_derive_retract). Defined.
#[refine] Global Instance retract_exp_exp_ite : retract (exp_ite exp) exp := ltac:(try_derive_retract). Defined.
#[refine] Global Instance retract_exp_exp_mut : retract (exp_mut exp) exp := ltac:(try_derive_retract). Defined.
#[refine] Global Instance retract_exp_exp_err : retract (exp_err exp) exp := ltac:(try_derive_retract). Defined.


#[represeted_as = retract_exp_exp_lam]
Elpi RegisterRepresented (retract_exp_exp_lam).

Check open_rec_lam.

Fixpoint open_rec (k : nat) (u : exp) (e : exp) : exp := 
    match e with 
        (* | In_exp_lam e => open_rec_lam _ open_rec k u e *)
        | In_exp_lam e => ltac:(elpi specialize_from_section open_rec_lam) k u e
        | In_exp_ite e => open_rec_ite _ open_rec k u e
        | In_exp_mut e => open_rec_mut _ open_rec k u e
        | In_exp_err e => open_rec_err _ open_rec k u e
    end
.

#[represeted_as = open_rec]
Elpi RegisterRepresented (open_rec).

Definition open_rec_lam' :=  ltac:(elpi specialize_from_section open_rec_lam).

Check open_rec_lam'.

Inductive lc' : nat -> exp -> Prop := 
    | lc_in_lam n e : lc'_lam _ lc' n e -> lc' n e
    | lc_in_ite n e : lc'_ite _ lc' n e -> lc' n e
    | lc_in_mut n e : lc'_mut _ lc' n e -> lc' n e
    | lc_in_err n e : lc'_err _ lc' n e -> lc' n e
.

#[represeted_as = lc']
Elpi RegisterRepresented (lc').

Definition retract_lc_revT exp_ext lc'_ext { retr : retract_f exp_ext exp} : Prop :=
    forall (n : nat) (e : exp_ext exp), lc' n (inj e) -> lc'_ext retr lc' n (inj e). 

Definition retract_lc_rev_lam : forall (n : nat) (e : exp_lam exp), lc' n (inj e) -> lc'_lam _ lc' n (inj e)
    := ltac:(intros n e; inversion 1; easy).


#[represeted_as = retract_lc_rev_lam]
Elpi RegisterRepresented (retract_lc_rev_lam).

#[represeted_as = retract_lc_lam]
Elpi RegisterRepresented (lc_in_lam).

Definition retract_lc_rev_ite : retract_lc_revT exp_ite (@lc'_ite exp) := ltac:(intros n e; inversion 1; easy).
Definition retract_lc_rev_mut : retract_lc_revT exp_mut (@lc'_mut exp) := ltac:(intros n e; inversion 1; easy).
Definition retract_lc_rev_err : retract_lc_revT exp_err (@lc'_err exp) := ltac:(intros n e; inversion 1; easy).

Definition retract_open_rec_rev exp_ext open_rec_ext  { retr : retract_f exp_ext exp } : Prop :=
    forall (n : nat) s (e : exp_ext exp), open_rec n s (inj e) = open_rec_ext retr open_rec n s e.


Definition retract_open_rec_rev_lam : forall (n : nat) s (e : exp_lam exp)
                                    , open_rec n s (inj e) = open_rec_lam exp open_rec n s e 
                                    := ltac:(intros; easy).

Definition retract_open_rec_rev_ite : forall (n : nat) s (e : exp_ite exp)
                                    , open_rec n s (inj e) = open_rec_ite exp open_rec n s e 
                                    := ltac:(intros; easy).

Definition retract_open_rec_rev_mut : forall (n : nat) s (e : exp_mut exp)
                                    , open_rec n s (inj e) = open_rec_mut exp open_rec n s e 
                                    := ltac:(intros; easy).

Definition retract_open_rec_rev_err : forall (n : nat) s (e : exp_err exp)
                                    , open_rec n s (inj e) = open_rec_err exp open_rec n s e 
                                    := ltac:(intros; easy).

#[represeted_as = retract_open_rec_rev_lam]
Elpi RegisterRepresented (retract_open_rec_rev_lam).

Fixpoint lc_weaken   : forall s n m, n <= m -> lc' n s -> lc' m s.
inversion 2; subst.
(* - apply (lc_weaken_lam exp _ lc_weaken lc_in_lam _) with (n := n); easy. *)
- apply (specialize_from_section lc_weaken_lam) with (n := n); easy.
- apply (lc_weaken_ite exp _ lc_weaken lc_in_ite _) with (n := n); easy.
- apply (lc_weaken_mut exp _ lc_weaken lc_in_mut _) with (n := n); easy.
- apply (lc_weaken_err exp _ lc_weaken lc_in_err _) with (n := n); easy.
Qed.

#[represeted_as = lc_weaken]
Elpi RegisterRepresented (lc_weaken).

Fixpoint open_rec_lc : forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
Proof.
inversion 2; subst.
(* - apply (open_rec_lc_lam exp open_rec retract_open_rec_rev_lam lc' open_rec_lc lc_weaken lc_in_lam); easy. *)
- apply (specialize_from_section open_rec_lc_lam); easy.
- apply (open_rec_lc_ite exp open_rec retract_open_rec_rev_ite lc' open_rec_lc lc_in_ite); easy.
- apply (open_rec_lc_mut exp open_rec retract_open_rec_rev_mut lc' open_rec_lc lc_in_mut); easy.
- apply (open_rec_lc_err exp open_rec retract_open_rec_rev_err lc' open_rec_lc lc_in_err); easy.
Qed.

#[represeted_as = open_rec_lc]
Elpi RegisterRepresented (open_rec_lc).

Inductive value : exp -> Prop := 
    | value_in_lam (e : exp) : (specialize_from_section value_lam) e -> value e
    | value_in_ite (e : exp) : value_ite _ e -> value e
    | value_in_mut (e : exp) : value_mut _ e -> value e
    | value_in_err (e : exp) : value_err _ e -> value e
.

#[represeted_as = value]
Elpi RegisterRepresented (value).

Fixpoint value_lc : forall v, value v -> lc' 0 v.
Proof.
    inversion 1; subst.
    - apply (value_lc_lam _ _); easy.
    - apply (value_lc_ite _ _ lc_in_ite); easy.
    - apply (value_lc_mut _ _ lc_in_mut); easy.
    - apply (value_lc_err _ _); easy.
Qed.

#[represeted_as = value_lc]
Elpi RegisterRepresented (value_lc).

Inductive tag := 
    | In_tag_lam : tag_lam -> tag
    | In_tag_ite : tag_ite -> tag
    | In_tag_mut : tag_mut -> tag
    | In_tag_err : tag_err -> tag
.

#[represeted_as = tag]
Elpi RegisterRepresented (tag).

#[refine] Global Instance retract_tag_tag_lam : retract tag_lam tag := ltac:(try_derive_retract). Defined. 
#[refine] Global Instance retract_tag_tag_ite : retract tag_ite tag := ltac:(try_derive_retract). Defined.
#[refine] Global Instance retract_tag_tag_mut : retract tag_mut tag := ltac:(try_derive_retract). Defined.
#[refine] Global Instance retract_tag_tag_err : retract tag_err tag := ltac:(try_derive_retract). Defined.

#[represeted_as = retract_tag_tag_lam]
Elpi RegisterRepresented (retract_tag_tag_lam).

Inductive tag_of : exp -> tag -> Prop := 
    | tag_of_in_lam e t: tag_of_lam _ _ e t -> tag_of e t
    | tag_of_in_ite e t: tag_of_ite _ _ e t -> tag_of e t
    | tag_of_in_mut e t: tag_of_mut _ _ e t -> tag_of e t
    | tag_of_in_err e t: tag_of_err _ _ e t -> tag_of e t 
.

#[represeted_as = tag_of]
Elpi RegisterRepresented (tag_of).

Lemma retract_tag_of_lam : forall (t : tag_lam) (e : exp_lam exp), tag_of (inj e) (inj t) <-> tag_of_lam _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

#[represeted_as = retract_tag_of_lam]
Elpi RegisterRepresented (retract_tag_of_lam).

Lemma retract_tag_of_ite : forall (t : tag_ite) (e : exp_ite exp), tag_of (inj e) (inj t) <-> tag_of_ite _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma retract_tag_of_mut: forall (t : tag_mut) (e : exp_mut exp), tag_of (inj e) (inj t) <-> tag_of_mut _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma retract_tag_of_err : forall (t : tag_err) (e : exp_err exp), tag_of (inj e) (inj t) <-> tag_of_err _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma tag_of_decidable e t : ~tag_of e t \/ tag_of e t.
Proof.
    destruct e; destruct t.
    all: try (rewrite retract_tag_of_lam; apply tag_of_decidable_lam).
    all: try (rewrite retract_tag_of_ite; apply tag_of_decidable_ite).
    all: try (rewrite retract_tag_of_mut; apply tag_of_decidable_mut).
    all: try (rewrite retract_tag_of_mut; apply tag_of_decidable_mut).
    all: try (rewrite retract_tag_of_err; apply tag_of_decidable_err).
    all: left; inversion 1; inversion H0.
Qed.

#[represeted_as = tag_of_decidable]
Elpi RegisterRepresented (tag_of_decidable).

From Imp Require Import context.

Definition VarEnv := Env (sig value).

Record Ctx := mkCtx {
        store : VarEnv;
}.

#[represeted_as = Ctx]
Elpi RegisterRepresented (Ctx).

#[refine] Global Instance ctx_supports_store : hasProj Ctx VarEnv := {
    get_proj := store;
    set_proj := (fun x c => mkCtx x);
}.
Proof.
    - intros. easy.
    - intros. destruct c. simpl. easy.
Defined.

#[represeted_as = ctx_supports_store]
Elpi RegisterRepresented (ctx_supports_store).

Inductive step : Ctx -> exp -> Ctx -> exp -> Prop := 
    (* | step_in_lam (c : Ctx) s c' s' : step_lam _ open_rec value _ step c s c' s' -> step c s c' s' *)
    | step_in_lam (c : Ctx) s c' s' : (specialize_from_section step_lam) c s c' s' -> step c s c' s'
    | step_in_ite (c : Ctx) s c' s' : step_ite _ _                step c s c' s' -> step c s c' s'
    | step_in_mut (c : Ctx) s c' s' : step_mut _ _ _              step c s c' s' -> step c s c' s'
    | step_in_err (c : Ctx) s c' s' : step_err _ _                step c s c' s' -> step c s c' s'
    (* interactions *)
    | step_in_lam_err (c : Ctx) s c' s' : step_int_lam_err _ value _ tag_of _ step c s c' s' -> step c s c' s'
    | step_in_ite_err (c : Ctx) s c' s' : step_int_ite_err _ value _ tag_of _ step c s c' s' -> step c s c' s'
    | step_in_mut_err (c : Ctx) s c' s' : step_int_mut_err _ value _ tag_of _ step c s c' s' -> step c s c' s'
.

#[represeted_as = step]
Elpi RegisterRepresented (step).

Definition lc := lc' 0.
Definition open := open_rec 0.

Fixpoint preservation : forall c e c' e',
    lc e ->
    step c e c' e' -> 
    lc e'. 
Proof. 
    (* intros *. *)
    intros c e c' e'.
    unfold lc in *.
    induction 2.
    (* - apply (preservation_lam exp open_rec lc' open_rec_lc lc_in_lam retract_lc_rev_lam value Ctx step preservation c s c' s'); easy. *)
    - apply ((specialize_from_section preservation_lam) c s c' s'); easy.
    - apply (preservation_ite exp lc' lc_in_ite retract_lc_rev_ite Ctx step preservation c s c' s'); easy.
    - apply (preservation_mut exp lc' lc_in_mut retract_lc_rev_mut value value_lc Ctx step preservation c s c' s'); easy.
    - apply (preservation_err exp lc' lc_in_err retract_lc_rev_err Ctx step preservation c s c' s'); easy.
    (* interactions *)
    - apply (preservation_lam_err exp lc' lc_in_err retract_lc_rev_lam retract_lc_rev_err value value_lc tag tag_of Ctx step preservation c s c' s'); easy.
    - apply (preservation_ite_err exp lc' lc_in_err retract_lc_rev_ite retract_lc_rev_err value value_lc tag tag_of Ctx step preservation c s c' s'); easy.
    - apply (preservation_mut_err exp lc' lc_in_mut lc_in_err retract_lc_rev_mut value tag tag_of Ctx step preservation c s c' s'); easy.
Defined.

#[represeted_as = preservation]
Elpi RegisterRepresented (preservation).

(* Fixpoint thing : forall c e c1' c2' e1' e2', lc e -> step c e c1' e1' -> step c e c2' e2' -> (c1' = c2' /\ e1' = e2'). *)
