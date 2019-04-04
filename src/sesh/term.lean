/- Introduces SGV terms and values. -/
import sesh.context
import sesh.matrix
import sesh.types
import sesh.mult


open matrix

inductive term: Π {γ}, context γ → tp → Type
| Var:
  Π {γ} {A: tp}
  (Γ: context γ)
  (x: γ ∋ A)
  (_: auto_param (Γ = identity γ A x) ``solve_context),
  -----------------------------------------------------
  term Γ A

| Abs:
  Π {γ} {Γ: context γ} {A B: tp},
  term (⟦1⬝A⟧::Γ) B
  ------------------
→ term Γ (A⊸B)

| App:
  Π {γ} {Γ₁ Γ₂: context γ} {A B: tp}
  (Γ: context γ)
  (M: term Γ₁ (A⊸B))
  (N: term Γ₂ A)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  term Γ B

| Unit:
  Π {γ}
  (Γ: context γ)
  (_: auto_param (Γ = 0) ``solve_context),
  ----------------------------------------
  term Γ tp.unit

| LetUnit:
  Π {γ} {Γ₁ Γ₂: context γ} {A: tp}
  (Γ: context γ)
  (M: term Γ₁ tp.unit)
  (N: term Γ₂ A)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  term Γ A

| Pair:
  Π {γ} {Γ₁ Γ₂: context γ} {A B: tp}
  (Γ: context γ)
  (M: term Γ₁ A)
  (N: term Γ₂ B)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  term Γ (tp.prod A B)

| LetPair:
  Π {γ} {Γ₁ Γ₂: context γ} {A B C: tp}
  (Γ: context γ)
  (M: term Γ₁ $ tp.prod A B)
  (N: term (⟦1⬝A⟧::⟦1⬝B⟧::Γ₂) C)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  term Γ C

| Inl:
  Π {γ} {Γ: context γ} {A: tp}
  (B: tp),
  term Γ A
  -------------------
→ term Γ (tp.sum A B)

| Inr:
  Π {γ} {Γ: context γ} {B: tp}
  (A: tp),
  term Γ B
  -------------------
→ term Γ (tp.sum A B)

| Case:
  Π {γ} {Γ₁ Γ₂: context γ} {A B C: tp}
  (Γ: context γ)
  (L: term Γ₁ $ tp.sum A B)
  (M: term (⟦1⬝A⟧::Γ₂) C)
  (N: term (⟦1⬝B⟧::Γ₂) C)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  term Γ C

| Fork:
  Π {γ} {Γ: context γ} {S: sesh_tp},
  term Γ (S⊸End!)
  -----------------------
→ term Γ (sesh_tp.dual S)

| Send:
  Π {γ} {Γ₁ Γ₂: context γ} {A: tp} {S: sesh_tp}
  (Γ: context γ)
  (M: term Γ₁ A)
  (N: term Γ₂ $ !A⬝S)
  (_: auto_param (Γ = Γ₁ + Γ₂) ``solve_context),
  ----------------------------------------------
  term Γ S

| Recv:
  Π {γ} {Γ: context γ} {A: tp} {S: sesh_tp},
  term Γ (?A⬝S)
----------------------
→ term Γ (tp.prod A S)

| Wait:
  Π {γ} {Γ: context γ},
  term Γ End?
  ---------------
→ term Γ tp.unit

open term

/- What it means for a term to be a value. Does not concern itself
   with configurations or channel names. -/
inductive value: ∀ {γ} {Γ: context γ} {A: tp}, term Γ A → Prop
| VVar: ∀ {γ} {A: tp}
  (Γ': context γ)
  (x: γ ∋ A)
  (_: auto_param (Γ' = identity γ A x) ``solve_context),
  ------------------------------------------------------
  value (Var Γ' x)

| VAbs:
  ∀ {γ} {Γ: context γ} {A B: tp}
  (M: term (⟦1⬝A⟧::Γ) B),
  -----------------------
  value (Abs M)

| VUnit:
  ∀ {γ}
  (Γ: context γ)
  (_: auto_param (Γ = 0) ``solve_context),
  ----------------------------------------
  value (Unit Γ)

| VPair:
  ∀ {γ} {Γ₁ Γ₂: context γ} {A B: tp}
    {M: term Γ₁ A} {N: term Γ₂ B}
  (Γ: context γ)
  /- This is not an auto_param for reasons that
    have to do with how Lean represents its
    constructors, a purely practical issue
    with the current implementation. -/
  (h: Γ = Γ₁ + Γ₂),
  value M
→ value N
  ----------------------------------------------
→ value (Pair Γ M N)

| VInl:
  ∀ {γ} {Γ: context γ} {A: tp} {M: term Γ A}
  (B: tp),
  value M
  ---------------
→ value (Inl B M)

| VInr:
  ∀ {γ} {Γ: context γ} {B: tp} {M: term Γ B}
  (A: tp),
  value M
  ---------------
→ value (Inr A M)
