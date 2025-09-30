From Imp Require Export header_extensible context.
From Stdlib Require Export Lists.List.


Section exp_mut.
    Variable exp : Type.

    Notation loc := nat.

    Inductive exp_mut : Type := 
        | exp_loc   : loc -> exp_mut
        | exp_setref   : exp -> exp -> exp_mut
        | exp_deref : exp -> exp_mut
        | exp_ref   : exp -> exp_mut
    .

    Context `{Hretr : retract exp_mut exp}.

    Definition exp_loc_ (n : nat) : _ := inj (exp_loc n).
    Definition exp_setref_ (e1 e2 : exp) : _ := inj (exp_setref e1 e2).
    Definition exp_deref_ (e : exp) : _ := inj (exp_deref e).
    Definition exp_ref_ (e : exp) : _ := inj (exp_ref e).

    Ltac unfold_mut :=
        match goal with
        | [ H : context [exp_loc_    ?x] |- _] => unfold exp_loc_ in H
        | [ H : context [exp_setref_ ?x] |- _] => unfold exp_setref_ in H
        | [ H : context [exp_deref_  ?x] |- _] => unfold exp_deref_ in H
        | [ H : context [exp_ref_    ?x] |- _] => unfold exp_ref_ in H
        | [ |- context [exp_loc_     ?x]] => unfold exp_loc_
        | [ |- context [exp_setref_  ?x]] => unfold exp_setref_
        | [ |- context [exp_deref_   ?x]] => unfold exp_deref_
        | [ |- context [exp_ref_     ?x]] => unfold exp_ref_
    end.

    Ltac simpl_inj := 
        repeat unfold_mut; match goal with 
            | [ H : inj ?x = inj ?y |- _ ] => apply retract_inj in H
        end
    .

    Variable open_rec : nat -> exp -> exp -> exp.

    Definition open_rec_mut (k : nat) (s : exp) (t : exp_mut) : exp := 
        match t with 
            | exp_loc n => inj (exp_loc n)
            | exp_setref v x => inj (exp_setref (open_rec k s x) (open_rec k s v))
            | exp_deref x => inj (exp_deref (open_rec k s x))
            | exp_ref x => inj (exp_ref (open_rec k s x))
        end
    .

    Variable retract_open_rec : forall (n : nat) s (e : exp_mut),
          open_rec n s (inj e) = open_rec_mut n s e.

    
    Variable lc' : nat -> exp -> Prop.
    Variable open_rec_lc : forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
    Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.


    Inductive lc'_mut : nat -> exp -> Prop := 
        | lc_loc n l   : lc'_mut n (exp_loc_ l)
        | lc_setref n v x : lc' n v -> lc' n x -> lc'_mut n (exp_setref_ v x)
        | lc_deref n x : lc' n x -> lc'_mut n (exp_deref_ x)
        | lc_ref n x   : lc' n x -> lc'_mut n (exp_ref_ x)
    .

    Variable retract_lc: forall n e, lc'_mut n e -> lc' n e.
    Variable retract_lc_rev: forall n e, lc' n (inj e) -> lc'_mut n (inj e).

    Definition lc_weaken_mut : forall s n m, n <= m -> lc'_mut n s -> lc' m s.
    Proof. 
        intros s n m le H0. destruct H0; apply retract_lc; constructor; apply lc_weaken with (n := n); easy.
    Defined.

    Definition open_rec_lc_mut : forall s t n, lc' 0 s -> lc'_mut (S n) t -> lc' n (open_rec n s t).
    Proof.
        intros s t n lc_s H0. inversion H0; subst;
        repeat unfold_mut;
        rewrite retract_open_rec; simpl;
        apply retract_lc; constructor; try apply open_rec_lc; try easy.
    Defined.

    Variable value : exp -> Prop.
    Variable value_lc : forall v, value v -> lc' 0 v.

    Inductive value_mut : exp -> Prop := 
        | value_loc l : value_mut (exp_loc_ l)
    .

    Definition value_lc_mut : forall v, value_mut v -> lc' 0 v.
    Proof.
        intros. induction H. apply retract_lc. constructor.
    Defined.

    Variable tag : Type.
    
    Inductive tag_mut := 
      | tag_loc  : tag_mut
    .

    Context `{Htag : retract tag_mut tag}.

    Definition tag_loc_ := inj tag_loc.

    Inductive tag_of_mut : exp -> tag -> Prop :=
      | tag_of_loc l : tag_of_mut (exp_loc_ l) tag_loc_
    .

    Lemma tag_of_decidable_mut : forall (e : exp_mut) (t : tag_mut), ~tag_of_mut (inj e) (inj t) \/ tag_of_mut (inj e) (inj t).
    Proof.
      intros. destruct e; destruct t;
      try (right; constructor).
      all: left; inversion 1.
      all: try apply retract_inj in H1.
      all: easy.
    Defined.

    Variable Ctx : Type.
    Context `{hasProj Ctx (Env (sig value))}.

    Variable step : Ctx -> exp -> Ctx -> exp -> Prop.
    Variable preservation : forall c e c' e', lc' 0 e -> step c e c' e' -> lc' 0 e'.
    

    Inductive step_mut : Ctx -> exp -> Ctx -> exp -> Prop := 
        (* set *)
        | step_setref c l v (vp : value v):
            Env.mem l (get_proj c) = true ->
            step_mut c 
                    (exp_setref_ (exp_loc_ l) v) 
                    (set_proj (Env.add l (exist _ v vp) (get_proj c)) c) 
                    (exp_loc_ l)
        | step_setref_red_l s c l c' l': 
            step c l c' l' -> 
            step_mut c (exp_setref_ l s) c' (exp_setref_ l' s)
        | step_setref_red l c s c' s': 
            step c s c' s' -> 
            step_mut c (exp_setref_ (exp_loc_ l) s) c' (exp_setref_ (exp_loc_ l) s')
        (* dereference *)
        | step_deref c l sig_v: 
            Env.find l (get_proj c) = Some sig_v -> 
            step_mut c (exp_deref_ (exp_loc_ l)) c (proj1_sig sig_v) 
        | step_deref_red c s c' s': 
            step c s c' s' -> step_mut c (exp_deref_ s) c (exp_deref_ s')
        (* reference *)
        | step_ref c v c' l : 
            Env.mem l (get_proj c) = false ->
            step_mut c (exp_ref_ v) c' (exp_loc_ l)
        | step_ref_red c s c' s': 
            step c s c' s' -> step_mut c (exp_ref_ s) c' (exp_ref_ s')
    .

    Definition preservation_mut : forall c e c' e', lc' 0 e -> step_mut c e c' e' -> lc' 0 e'.
    Proof.
        intros c e c' e' lc_e.
        induction 1. 
        - apply retract_lc. constructor.
        - apply retract_lc_rev in lc_e. inversion lc_e; subst; try simpl_inj; try easy.
          apply retract_lc. constructor.
            + inversion H1. subst. apply (preservation _ _ _ _ H2 H0).
            + inversion H1. subst. easy.
        - apply retract_lc_rev in lc_e. inversion lc_e; subst; try simpl_inj; try easy.
          apply retract_lc. constructor.
            + apply retract_lc. constructor.
            + inversion H1. subst. apply (preservation _ _ _ _ H4 H0).
        - destruct sig_v. simpl. 
          apply value_lc. easy.
        - apply retract_lc_rev in lc_e. inversion lc_e; subst; try simpl_inj; try easy.
          inversion H1. subst. apply retract_lc. constructor. apply (preservation _ _ _ _ H3 H0).
        - unfold exp_loc_. apply retract_lc. constructor.
        - unfold exp_ref_. apply retract_lc. constructor. 
          apply retract_lc_rev in lc_e. inversion lc_e; subst; try simpl_inj; try easy.
          inversion H1. subst.
          apply (preservation c s c' s'); easy.
    Defined.

End exp_mut.