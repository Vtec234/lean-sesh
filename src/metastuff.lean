/- Meta stuff: attributes, tactics, etc. -/


/-
@[user_attribute]
meta def sop_attr: user_attribute :=
{ name := `sop_form,
  descr := "A simplification lemma that brings expressions to a sum-of-products form." } -/

run_cmd mk_simp_attr `sop_form [`simp]

/-
@[user_attribute]
meta def unfold_attr: user_attribute :=
{ name := `unfold_,
  descr := "Essentially what unfold should do but doesn't so I use simp instead." } -/

run_cmd mk_simp_attr `unfold_ [`simp]

meta def solve_context: tactic unit :=
  `[simp * with unfold_ sop_form, try { simp * with unfold_ sop_form },
    done <|> tactic.fail "Cannot prove contexts equal." ]
