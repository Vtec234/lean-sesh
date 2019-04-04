/- Introduces matrices and horrifying linear algebra. -/

import qtt.context

open context
open debrujin_idx


/- This matrix defines the context in which every variable (given by a debrujin idx)
   exists. In other words, it defines a substitution. Variables all exist in the same
   precontext, but the type multiplicities might differ. -/
def matrix (τ mult: Type) (γ δ: precontext τ)
  : Type := Π (T: τ), γ ∋ T → @context τ mult δ

namespace matrix

variable {τ: Type}
variables {mult: Type} [semiring mult]

def identity: Π γ, @matrix τ mult γ γ
| (T::δ) _ ZVar := ⟦1⬝T⟧::0
| (T::δ) U (SVar x) := ⟦0⬝T⟧::(identity δ U x)

@[unfold_] lemma identity_zvar {T: τ} {γ: precontext τ}
  : identity (T::γ) T ZVar = ⟦(1: mult)⬝T⟧::(0: context γ) := by refl

@[unfold_] lemma identity_svar {T U: τ} {δ: precontext τ} {x}
  : identity (T::δ) U (SVar x) = ⟦(0: mult)⬝T⟧::(identity δ U x) := by refl

def vmul: ∀ {γ δ}, @context τ mult γ → @matrix τ mult γ δ → @context τ mult δ
| _ δ context.nil _ := 0
| _ _ (⟦π⬝T⟧::Γ) Ξ := (π • Ξ T ZVar) + (vmul Γ (λ U x, Ξ U (SVar x)))

infix ` ⊛ `:70 := vmul

namespace vmul

@[simp] lemma vmul_nil {δ} {Ξ: @matrix τ mult [] δ}
  : context.nil ⊛ Ξ = 0 := by refl

@[unfold_] lemma vmul_cons {γ δ} {T: τ} {Γ: context γ} {π: mult} {Ξ: @matrix τ mult (T::γ) δ}
  : ⟦π⬝T⟧::Γ ⊛ Ξ = (π • Ξ T ZVar) + (Γ ⊛ (λ U x, Ξ U (SVar x))) :=
    by refl

@[simp] lemma zero_vmul
  : ∀ {γ δ: precontext τ} (M: @matrix τ mult γ δ),
    0 ⊛ M = 0 :=
begin
  intros,
  induction γ with T γ ih,
  { refl },
  { unfold has_zero.zero zeros,
    simp * with unfold_,
    show (0: mult) • M T ZVar + 0 ⊛ (λ (U: τ) (x: γ ∋ U), M U (SVar x)) = 0,
    simp * },
end

@[simp] lemma vmul_ext_zero
  : ∀ {γ δ} {Γ: context γ} {Ξ: @matrix τ mult γ δ} {T: τ},
    Γ ⊛ (λ U x, ⟦0⬝T⟧::(Ξ U x)) = ⟦0⬝T⟧::(Γ ⊛ Ξ) :=
begin
  intros,
  induction Γ with γ' π T' Γ ih,
  { refl },
  { simp * with unfold_ },
end

@[simp] lemma one_vmul
  : ∀ {γ δ} {Ξ: @matrix τ mult γ δ} {T: τ}
    (x: γ ∋ T),
    -------------------------------
    (identity γ T x) ⊛ Ξ = Ξ T x :=
begin
  intros,
  induction x with γ' T' δ' T'' U x' ih;
  { simp * with unfold_ },
end

@[simp] lemma vmul_one
  : ∀ {γ} (Γ: @context τ mult γ),
    Γ ⊛ (identity γ) = Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { simp [*, vmul_ext_zero] with unfold_ },
end

lemma smul_vmul
  : ∀ {γ δ} {Γ: @context τ mult γ} {Ξ: @matrix τ mult γ δ} {π: mult},
    (π • Γ) ⊛ Ξ = π • (Γ ⊛ Ξ) :=
begin
  intros,
  induction Γ with γ' π' T Γ ih;
  { simp [*, context.mul_smul]
    with unfold_ sop_form },
end

@[sop_form] lemma vmul_right_distrib
  : ∀ {γ δ} {Γ₁ Γ₂: @context τ mult γ} {Ξ: @matrix τ mult γ δ},
    (Γ₁ + Γ₂) ⊛ Ξ = (Γ₁ ⊛ Ξ) + (Γ₂ ⊛ Ξ) :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁;
  { cases Γ₂,
    simp * with unfold_ sop_form },
end

end vmul

end matrix
