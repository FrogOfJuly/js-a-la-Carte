From elpi Require Import elpi.

Elpi Db section_template.db lp:{{

  pred is_section_template o:string.
  pred section_template_vars o:string o:list (pair string term).

  % the Db is empty for now, we put a rule giving a
  % descriptive error and we name that rule "age.fail".
  :name "is_section_template.fail"
  is_section_template Name :- coq.error "I don't know who" Name "is!".

  :name "section_template_vars.fail"
  section_template_vars Name _ :- coq.error "I don't know this section tempalte:" Name.

}}.


Elpi Command print_all_section_template.
Elpi Accumulate Db section_template.db.
Elpi Accumulate lp:{{

  :before "is_section_template.fail"
  is_section_template _ :- !, fail. % softly

  main [] :-
    std.findall (is_section_template _) Rules,
    std.forall Rules print-rule.

  pred print-rule i:prop.
  print-rule (is_section_template P) :- coq.say "found" P .

}}.

Elpi Command print_all_section_template_vars.
Elpi Accumulate Db section_template.db.
Elpi Accumulate lp:{{

  :before "section_template_vars.fail"
  section_template_vars _ _ :- !, fail. % softly

  main [] :-
    std.findall (section_template_vars _ _) Rules,
    std.forall Rules print-rule.

  pred print-rule i:prop.
  print-rule (section_template_vars P N) :- coq.say "Section" P "has these vars" N.

}}.

Elpi Command SectionTemplate.
#[synterp] Elpi Accumulate lp:{{ 
  main [str "Section", str SectionName]
  :-  coq.say "synterop: Found section template:" SectionName
    , coq.env.begin-section SectionName
    .
  main [str "End", str SectionName]
  :-  coq.say "synterop: Ending section template:" SectionName
    , coq.env.end-section
    .
}}.
Elpi Accumulate Db section_template.db.
Elpi Accumulate lp:{{ 

  :before "is_section_template.fail"
  is_section_template _ :- !, fail. % softly

  :before "section_template_vars.fail"
  section_template_vars _ _ :- !, fail. % softly
  
  main [str "Section", str SectionName]
  :-  coq.say "Found section template:" SectionName
    , if (is_section_template SectionName) (coq.error "Template with this name exists:" SectionName) true
    , TheNewRule = is_section_template SectionName
    , coq.env.begin-section SectionName
    , coq.elpi.accumulate _ "section_template.db" (clause _ (before "is_section_template.fail") TheNewRule)
    , coq.say "Printing:"
    , coq.say "Added new template" SectionName
    .
  main [str "End", str SectionName]
  :-  coq.say "Ending section template:" SectionName
    , coq.env.section Variables
    , std.map Variables (x\ r\ coq.typecheck (global (const x)) r ok) VariableTys
    , std.map Variables (x\ r\ r is {coq.term->string (global (const x))}) Variables'
    , std.zip Variables' VariableTys R
    , coq.say "Variables:" R
    , TheNewRule = section_template_vars SectionName R
    , coq.elpi.accumulate _ "section_template.db" (clause _ (before "section_template_vars.fail") TheNewRule)
    , coq.env.current-section-path SecPath
    , if (std.rev SecPath (SectionName::_)) true (coq.error "Trying to close mismatching section:" SectionName "Current section path:" SecPath)
    , coq.env.end-section
    .
  main Args 
  :-  coq.say "What do: " Args
    .
}}.

Elpi Command FollowSectionTemplate.
#[synterp] Elpi Accumulate lp:{{ 
  main [str "Section", str SectionName]
  :-  coq.say "synterop: Follow template:" SectionName
    , coq.env.begin-section SectionName
  .
  main [str "End", str SectionName]
  :-  coq.say "synterop: Ending Follow section:" SectionName
    , coq.env.end-section
    .
}}.
Elpi Accumulate Db section_template.db.
Elpi Accumulate lp:{{  
  :before "is_section_template.fail"
  is_section_template _ :- !, fail. % softly

  :before "section_template_vars.fail"
  section_template_vars _ _ :- !, fail. % softly

func declare_variable i:(pair string term) .
declare_variable (pr N Ty) 
:-  coq.say "Declaring" N Ty
  , coq.env.add-section-variable N _ Ty _
  , coq.say "more things should be done"
  .

main [str "Section", str SectionName]
:-  coq.say "Following section template for " SectionName
  , coq.env.begin-section SectionName
  , std.findall (is_section_template _) KnownSectionTemplates
  , coq.say "Found know section templates" KnownSectionTemplates
  , std.mem! KnownSectionTemplates (is_section_template SectionName)
  , std.findall (section_template_vars SectionName _) SectionVariables
  , coq.say "Found section variables:" SectionVariables
  , std.mem SectionVariables (section_template_vars SectionName Variables)
  , coq.say "Found vars:" Variables
  , std.forall Variables declare_variable
  .
main [str "End", str SectionName]
:- coq.env.current-section-path SecPath
 , if (std.rev SecPath (SectionName::_)) true (coq.error "Trying to close mismatching section:" SectionName "Current section path:" SecPath)
 , if (is_section_template SectionName)  true (coq.error "Trying to close section that does not exist:" SectionName) 
 , coq.env.end-section
 .
}}.


Elpi SectionTemplate
Section exp_lam'.

  Variable exp : Type.
  Variable open_rec : nat -> exp -> exp -> exp.
  Variable lc' : nat -> exp -> Prop.
  Variable open_rec_lc :forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
  Variable lc_weaken   : forall s n m, n <= m  -> lc' n s -> lc' m s.

Elpi SectionTemplate
End exp_lam'.

Elpi FollowSectionTemplate
Section exp_lam'.


Lemma foo : exp -> nat.
Proof.
Admitted.

Elpi FollowSectionTemplate
End exp_lam'.