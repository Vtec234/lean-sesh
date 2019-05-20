/- Introduces evaluation contexts. -/

import sesh.term
import sesh.ren_sub

open term
open matrix

universes u v w

/- Oh no, additional axioms. -/
axiom heq.congr {α γ : Sort u} {β δ : Sort v} {f₁ : α → β} {f₂ : γ → δ} {a₁ : α} {a₂ : γ} (h₁ : f₁ == f₂) (h₂ : a₁ == a₂) : f₁ a₁ == f₂ a₂

axiom heq.dcongr {α β : Sort u} {γ δ : Sort v} {ε ζ : Sort w} {f₁ : Π α, γ → ε} {f₂ : Π β, δ → ζ} {a₁₁ : α} {a₁₂ : γ} {a₂₁ : β} {a₂₂ : δ} (h₁ : f₁ == f₂) (h₂ : a₁₁ == a₂₁) (h₃ : a₁₂ == a₂₂) : f₁ a₁₁ a₁₂ == f₂ a₂₁ a₂₂

/- The context except the hole consumes Γₑ resources, while the
   hole can consume arbitrary resources Γ. The term plugged in
   for the hole must have type A' (hence the hole is "typed") and
   the resulting term has type A. In every evaluation context,
   the hole has the same precontext as the overall expression,
   since GV never evaluates under binders. Therefore I don't have
   to allow a fully general (i.e. arbitrary precontext) typing
   context for the hole. -/
@[reducible]
def eval_ctx_fn {γ} (Γₑ: context γ) (A' A: tp): Type :=
  Π (Γ: context γ), term Γ A' → term (Γ + Γₑ) A

namespace eval_ctx_fn

@[reducible]
def apply {γ} {Γₑ Γ': context γ} {A' A: tp}
  (f: eval_ctx_fn Γₑ A' A)
  (Γ: context γ)
  (M: term Γ' A')
  (h: auto_param (Γ = Γ'+Γₑ) ``solve_context)
  : term Γ A :=
cast (by solve_context) $ f Γ' M

end eval_ctx_fn

/- A value of type (eval_ctx f) specifies that f is a valid function
   for an evaluation context. It's a Type rather than a Prop, because
   Prop can only eliminate into Prop but sometimes I need to extract
   the actual value of a constructor argument out of an eval_ctx. -/
inductive eval_ctx
  : Π {γ} {A' A: tp} (Γₑ: context γ), eval_ctx_fn Γₑ A' A → Type
| EHole:
  Π (γ: precontext) (A: tp),
  eval_ctx 0 (λ (Γ: context γ) (M: term Γ A), begin convert M, solve_context end)

| EAppLeft:
  Π {γ} {Γ₁ Γ₂: context γ} {A B: tp}
    {C'}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (N: term Γ₂ A)
  (E: eval_ctx_fn Γ₁ C' $ A⊸B),
  eval_ctx Γ₁ E
  -------------------------------
→ eval_ctx Γₑ (λ Γ M, App _ (E Γ M) N)

| EAppRight:
  Π {γ} {Γ₁ Γ₂: context γ} {A B: tp}
    {A'} {V: term Γ₁ $ A⊸B}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (hV: value V)
  (E: eval_ctx_fn Γ₂ A' A),
  eval_ctx Γ₂ E
  -------------------------------
→ eval_ctx Γₑ (λ Γ M, App _ V $ E Γ M)

| ELetUnit:
  Π {γ} {Γ₁ Γ₂: context γ} {A: tp}
    {A'}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (N: term Γ₂ A)
  (E: eval_ctx_fn Γ₁ A' tp.unit),
  eval_ctx Γ₁ E
  ---------------------------------
→ eval_ctx Γₑ (λ Γ M, LetUnit _ (E Γ M) N)

| EPairLeft:
  Π {γ} {Γ₁ Γ₂: context γ} {A B: tp}
    {A'}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (N: term Γ₂ B)
  (E: eval_ctx_fn Γ₁ A' A),
  eval_ctx Γ₁ E
  ------------------------------
→ eval_ctx Γₑ (λ Γ M, Pair _ (E Γ M) N)

| EPairRight:
  Π {γ} {Γ₁ Γ₂: context γ} {A B: tp}
    {B'} {V: term Γ₁ A}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (hV: value V)
  (E: eval_ctx_fn Γ₂ B' B),
  eval_ctx Γ₂ E
  ------------------------------
→ eval_ctx Γₑ (λ Γ M, Pair _ V $ E Γ M)

| ELetPair:
  Π {γ} {Γ₁ Γ₂: context γ} {A B C: tp}
    {C'}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (N: term (⟦1⬝A⟧::⟦1⬝B⟧::Γ₂) C)
  (E: eval_ctx_fn Γ₁ C' $ tp.prod A B),
  eval_ctx Γ₁ E
  ----------------------------------
→ eval_ctx Γₑ (λ Γ M, LetPair _ (E Γ M) N)

| EInl:
  Π {γ} {Γₑ: context γ} {A: tp}
    {A'}
  (B: tp)
  (E: eval_ctx_fn Γₑ A' A),
  eval_ctx Γₑ E
  -----------------------------
→ eval_ctx Γₑ (λ Γ M, Inl B $ E Γ M)

| EInr:
  Π {γ} {Γₑ: context γ} {B: tp}
    {B'}
  (A: tp)
  (E: eval_ctx_fn Γₑ B' B),
  eval_ctx Γₑ E
  ---------------------------
→ eval_ctx Γₑ (λ Γ M, Inr A $ E Γ M)

| ECase:
  Π {γ} {Γ₁ Γ₂: context γ} {A B C: tp}
    {D'}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (M: term (⟦1⬝A⟧::Γ₂) C)
  (N: term (⟦1⬝B⟧::Γ₂) C)
  (E: eval_ctx_fn Γ₁ D' $ tp.sum A B),
  eval_ctx Γ₁ E
  --------------------------------
→ eval_ctx Γₑ (λ Γ L, Case _ (E Γ L) M N)

| EFork:
  Π {γ} {Γₑ: context γ} {S: sesh_tp}
    {T'}
  (E: eval_ctx_fn Γₑ T' $ S⊸End!),
  eval_ctx Γₑ E
  --------------------------
→ eval_ctx Γₑ (λ Γ x, Fork (E Γ x))

| ESendLeft:
  Π {γ} {Γ₁ Γ₂: context γ} {A: tp} {S: sesh_tp}
    {A'}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (N: term Γ₂ $ !A⬝S)
  (E: eval_ctx_fn Γ₁ A' A),
  eval_ctx Γ₁ E
  ------------------------------
→ eval_ctx Γₑ (λ Γ M, Send _ (E Γ M) N)

| ESendRight:
  Π {γ} {Γ₁ Γ₂: context γ} {A: tp} {S: sesh_tp}
    {T'} {V: term Γ₁ A}
  (Γₑ: context γ)
  (hΓ: Γₑ = Γ₁ + Γ₂)
  (hV: value V)
  (E: eval_ctx_fn Γ₂ T' $ !A⬝S),
  eval_ctx Γ₂ E
  ------------------------------
→ eval_ctx Γₑ (λ Γ M, Send _ V $ E Γ M)

| ERecv:
  Π {γ} {Γₑ: context γ} {A: tp} {S: sesh_tp}
    {T'}
  (E: eval_ctx_fn Γₑ T' ?A⬝S),
  eval_ctx Γₑ E
  --------------------------
→ eval_ctx Γₑ (λ Γ M, Recv $ E Γ M)

| EWait:
  Π {γ} {Γₑ: context γ}
    {T'}
  (E: eval_ctx_fn Γₑ T' End?),
  eval_ctx Γₑ E
  --------------------------
→ eval_ctx Γₑ (λ Γ M, Wait $ E Γ M)

namespace eval_ctx
open matrix.vmul

/- The new function we're defining takes a hole term defined over
   an extended environment (rename ρ Γ) and returns the same expression,
   but well-typed under the extended environment. -/
def ext:
    Π {γ δ: precontext}  {A' A: tp}{Γ: context γ}
      {E: eval_ctx_fn Γ A' A}
    (ρ: ren_fn γ δ),
    eval_ctx Γ E
    -----------------------------------------------
  → Σ E': eval_ctx_fn (Γ ⊛ (λ B x, identity δ B $ ρ B x)) A' A,
      eval_ctx (Γ ⊛ (λ B x, identity δ B $ ρ B x)) E'
/- In each case we define what happens when the resulting
   renamed evaluation context is _applied_ to a hole-filling
   argument, which is the last matched variable (usually M).

   Most cases proceed by renaming parts of the evaluation context
   to make sense in the extended typing context and proving that
   the contexts still make sense.

   The return value of this function also carries the proof
   that the returned function is, in fact, an evaluation context. -/
| _ _ _ _ _ _ _ (EHole _ _) :=
begin
  rw [matrix.vmul.zero_vmul],
  exact ⟨_, EHole _ _⟩
end
| _ _ _ _ _ _ ρ (EAppLeft _ hΓ N _ E) :=
  let E' := ext ρ E in
  ⟨_, EAppLeft
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (rename ρ _ N)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EAppRight _ hΓ hV _ E) :=
  let E' := ext ρ E in
  ⟨_, EAppRight
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (hV.rename ρ)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (ELetUnit _ hΓ N _ E) :=
  let E' := ext ρ E in
  ⟨_, ELetUnit
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (rename ρ _ N)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EPairLeft _ hΓ N _ E) :=
  let E' := ext ρ E in
  ⟨_, EPairLeft
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (rename ρ _ N)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EPairRight _ hΓ hV _ E) :=
  let E' := ext ρ E in
  ⟨_, EPairRight
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (hV.rename ρ)
    E'.fst
    E'.snd⟩
| γ _ _ _ _ _ ρ (ELetPair _ hΓ N _ E) :=
  let E' := ext ρ E in
  ⟨_, ELetPair
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (rename ((ρ.ext _).ext _) _ N)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EInl C _ E) :=
  let E' := ext ρ E in
  ⟨_, EInl
    C
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EInr C _ E) :=
  let E' := ext ρ E in
  ⟨_, EInr
    C
    E'.fst
    E'.snd⟩
| γ _ _ _ _ _ ρ (ECase _ hΓ M N _ E) :=
  let E' := ext ρ E in
  ⟨_, ECase
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (rename (ρ.ext _) _ M)
    (rename (ρ.ext _) _ N)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EFork _ E) :=
  let E' := ext ρ E in
  ⟨_, EFork
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (ESendLeft _ hΓ N _ E) :=
  let E' := ext ρ E in
  ⟨_, ESendLeft
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (rename ρ _ N)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (ESendRight _ hΓ hV _ E) :=
  let E' := ext ρ E in
  ⟨_, ESendRight
    _
    (begin rw [hΓ, vmul_right_distrib] end)
    (hV.rename ρ)
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (ERecv _ E) :=
  let E' := ext ρ E in
  ⟨_, ERecv
    E'.fst
    E'.snd⟩
| _ _ _ _ _ _ ρ (EWait _ E) :=
  let E' := ext ρ E in
  ⟨_, EWait
    E'.fst
    E'.snd⟩

def wrap: Π {γ} {A'' A' A: tp} {Γₑ Γₑ': context γ}
  (E: eval_ctx_fn Γₑ A'' A')
  (hE: eval_ctx Γₑ E)
  (E': eval_ctx_fn Γₑ' A' A)
  (hE': eval_ctx Γₑ' E')
  (Γ: context γ)
  (hΓ: Γ = Γₑ+Γₑ'),
  Σ E': eval_ctx_fn Γ A'' A,
      eval_ctx Γ E'
| _ _ _ _ _ _ E hE _ (EHole _ _) Γ hΓ :=
  cast (begin congr; simp [*, hΓ], congr' 1, simp [hΓ] end)
    (sigma.mk E hE)
| _ _ _ _ _ _ E hE _ (EAppLeft _ _ N E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EAppLeft Γ (by solve_context) N EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EAppRight _ _ hV E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EAppRight Γ (by solve_context) hV EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (ELetUnit _ _ N E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, ELetUnit Γ (by solve_context) N EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EPairLeft _ _ N E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EPairLeft Γ (by solve_context) N EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EPairRight _ _ hV E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EPairRight Γ (by solve_context) hV EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (ELetPair _ _ N E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, ELetPair Γ (by solve_context) N EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EInl B E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EInl B (cast (by rw [hΓ]) EE'.fst) $ cast (begin
    congr' 1, exact hΓ.symm,
    h_generalize Hx: EE'.fst == x, exact Hx,
  end) EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EInr A E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EInr A (cast (by rw [hΓ]) EE'.fst) $ cast (begin
    congr' 1, exact hΓ.symm,
    h_generalize Hx: EE'.fst == x, exact Hx,
  end) EE'.snd⟩
| _ _ _ _ _ _ E hE _ (ECase _ _ M N E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, ECase Γ (by solve_context) M N EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EFork E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EFork (cast (by rw [hΓ]) EE'.fst) $ cast (begin
    congr' 1, exact hΓ.symm,
    h_generalize Hx: EE'.fst == x, exact Hx,
  end) EE'.snd⟩
| _ _ _ _ _ _ E hE _ (ESendLeft _ _ M E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, ESendLeft Γ (by solve_context) M EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (ESendRight _ _ hV E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, ESendRight Γ (by solve_context) hV EE'.fst EE'.snd⟩
| _ _ _ _ _ _ E hE _ (ERecv E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, ERecv (cast (by rw [hΓ]) EE'.fst) $ cast (begin
    congr' 1, exact hΓ.symm,
    h_generalize Hx: EE'.fst == x, exact Hx,
  end) EE'.snd⟩
| _ _ _ _ _ _ E hE _ (EWait E' hE') Γ hΓ :=
  let EE' := wrap E hE E' hE' _ rfl in
  ⟨_, EWait (cast (by rw [hΓ]) EE'.fst) $ cast (begin
    congr' 1, exact hΓ.symm,
    h_generalize Hx: EE'.fst == x, exact Hx,
  end) EE'.snd⟩

set_option pp.implicit true

lemma wrap_composes {γ} {Γ Γₑ Γₑ': context γ} {A'' A' A: tp}
    {M: term Γ A''}
    {E': eval_ctx_fn Γₑ A'' A'}
    {hE': eval_ctx Γₑ E'}
    {E: eval_ctx_fn Γₑ' A' A}
    {hE: eval_ctx Γₑ' E}
  (Γ': context γ)
  (hΓ': Γ' = Γ+Γₑ)
  (EM: term Γ' A')
  (Γ'': context γ)
  (hΓ'': Γ'' = Γ'+Γₑ')
  (EM': term Γ'' A)
  (hEM: EM = E'.apply Γ' M)
  (hEM': EM' = E.apply Γ'' EM)
  : EM' = (wrap E' hE' E hE _ rfl).fst.apply Γ'' M :=
begin
  induction hE; simp [*, wrap, eval_ctx_fn.apply],
  case EHole {
    h_generalize Hx: (E' Γ M) == x,
    h_generalize Hy: x == y,
    h_generalize Hx': (⟨E', hE'⟩: Σ E': eval_ctx_fn Γₑ A'' hE_A, eval_ctx Γₑ E') == x',
    congr' 1, simp [hΓ'],
    apply heq.trans Hy.symm, apply heq.trans Hx.symm,
    apply heq.congr, unfold sigma.fst,
    sorry
  },
  sorry
end

end eval_ctx

/- An evaluation context is a hole-replacing function
   together with a proof of its validity. -/
structure eval_ctx' {γ} (Γₑ: context γ) (A' A: tp) :=
(f: eval_ctx_fn Γₑ A' A)
(h: eval_ctx Γₑ f)

namespace eval_ctx'

def ext {γ δ: precontext} {Γ: context γ} {A' A: tp} (ρ: ren_fn γ δ) (E: eval_ctx' Γ A' A)
  : eval_ctx' (Γ ⊛ (λ B x, identity δ B $ ρ B x)) A' A :=
  let E' := eval_ctx.ext ρ E.h in
  ⟨E'.fst, E'.snd⟩

def wrap {γ} {Γₑ Γₑ': context γ} {A'' A' A: tp}
  (E: eval_ctx' Γₑ A'' A')
  (E': eval_ctx' Γₑ' A' A)
  (Γ: context γ)
  (hΓ: Γ = Γₑ+Γₑ')
  : eval_ctx' Γ A'' A :=
let EE' := eval_ctx.wrap E.f E.h E'.f E'.h Γ hΓ in
⟨EE'.fst, EE'.snd⟩

lemma wrap_composes {γ} {Γ Γₑ Γₑ': context γ} {A'' A' A: tp}
    {M: term Γ A''}
    {E': eval_ctx' Γₑ A'' A'}
    {E: eval_ctx' Γₑ' A' A}
  (Γ': context γ)
  (hΓ': Γ' = Γ+Γₑ)
  (EM: term Γ' A')
  (Γ'': context γ)
  (hΓ'': Γ'' = Γ'+Γₑ')
  (EM': term Γ'' A)
  (hE: EM = E'.f.apply Γ' M)
  (hE': EM' = E.f.apply Γ'' EM)
  : EM' = (E'.wrap E _ rfl).f.apply Γ'' M :=
sorry

end eval_ctx'

inductive term_reduces
  : ∀ {γ} {Γ: context γ} {A: tp}, term Γ A → term Γ A → Prop
infix ` ⟶M `:55 := term_reduces
| EvalLift:
  ∀ {γ} {Γ Γₑ: context γ} {A A': tp}
    {M M': term Γ A}
  (Γ': context γ)
  (E: eval_ctx' Γₑ A A')
  (EM EM': term Γ' A')
  (hΓ': Γ' = Γ+Γₑ)
  (hStep: M ⟶M M')
  (hEM: EM = E.f.apply Γ' M)
  (hEM': EM' = E.f.apply Γ' M'),
  -----------------------
  EM ⟶M EM'

| EvalLam:
  ∀ {γ} {Γ₁ Γ₂: context γ} {A B: tp}
    {V: term Γ₂ A}
  (Γ: context γ)
  (M: term (⟦1⬝A⟧::Γ₁) B)
  (hV: value V)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  (App Γ (Abs M) V) ⟶M ssubst _ M V

| EvalUnit:
  ∀ {γ} {Γ: context γ} {A: tp}
  (M: term Γ A),
  ---------------------------------------
  (LetUnit Γ (Unit 0) M $ by simp) ⟶M M

| EvalPair:
  ∀ {γ} {Γ₁₁ Γ₁₂ Γ₂: context γ} {A B C: tp}
    {V: term Γ₁₁ A} {W: term Γ₁₂ B}
  (Γ₁ Γ: context γ)
  (hV: value V)
  (hW: value W)
  (M: term (⟦1⬝A⟧::⟦1⬝B⟧::Γ₂) C)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context)
  (_: auto_param (Γ₁ = Γ₁₁ + Γ₁₂) ``solve_context),
  -----------------------------------------------------------
  (LetPair Γ (Pair Γ₁ V W $ by assumption) M $ by assumption)
  ⟶M
  dsubst _ M V W

| EvalInl:
  ∀ {γ} {Γ₁ Γ₂: context γ} {A B C: tp}
    {V: term Γ₁ A}
  (Γ: context γ)
  (hV: value V)
  (M: term (⟦1⬝A⟧::Γ₂) C)
  (N: term (⟦1⬝B⟧::Γ₂) C)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  (Case Γ (Inl B V) M N) ⟶M ssubst _ M V

| EvalInr:
  ∀ {γ} {Γ₁ Γ₂: context γ} {A B C: tp}
    {V: term Γ₁ B}
  (Γ: context γ)
  (hV: value V)
  (M: term (⟦1⬝A⟧::Γ₂) C)
  (N: term (⟦1⬝B⟧::Γ₂) C)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  (Case Γ (Inr A V) M N) ⟶M ssubst _ N V

infix ` ⟶M `:55 := term_reduces

/- This is what I thought initially (WRONG!):
   I _think_ there is barely any benefit to formalizing evaluation contexts
   because they would have to be defined for all kinds of terms anyway.

   Actually no, eval_ctx is _necessary_ to formalize configuration reduction
   without losing what's left of my sanity. -/
