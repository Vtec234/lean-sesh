/- Introduces matrices and horrifying linear algebra. -/

import sesh.context

open context
open debrujin_idx


/- For every variable (given by a debrujin idx), a matrix gives the context
   required by that variable. This is used when simultaneously substituting
   a bunch of terms for variables - the context required by the post-subst
   term will be Γ ⊛ Ξ, where Γ is the pre-subst context and Ξ defines the
   substitution. -/
def matrix (γ δ: precontext)
  : Type := Π (T: tp), γ ∋ T → context δ

namespace matrix

def identity: Π γ, matrix γ γ
| (T::_) _ (ZVar _ _) := ⟦1⬝T⟧::0
| (T::γ') U (SVar .(T) x) := ⟦0⬝T⟧::(identity γ' U x)

@[unfold_] lemma identity_zvar {T: τ} {γ: precontext}
  : identity (T::γ) T (ZVar _ T) = ⟦(1: mult)⬝T⟧::(0: context γ) := by refl

@[unfold_] lemma identity_svar {T U: τ} {δ: precontext} {x}
  : identity (T::δ) U (SVar T x) = ⟦(0: mult)⬝T⟧::(identity δ U x) := by refl

lemma identity_neq_zero {γ: precontext} {A: tp} {x: γ ∋ A}
  : identity γ A x ≠ 0 :=
begin
  intro h, unfold has_zero.zero at h, induction x,
  { simp [zeros] with unfold_ at h, cases h.left },
  case SVar : _ _ _ _ ih {
    simp [zeros, identity] at h, exact ih h },
end

def vmul: ∀ {γ δ}, context γ → matrix γ δ → context δ
| _ _ context.nil _ := 0
| (_::γ) _ (⟦π⬝T⟧::Γ) Ξ := (π • Ξ T (ZVar γ T)) + (vmul Γ (λ U x, Ξ U (SVar T x)))
infix ` ⊛ `:70 := vmul

/- Extend a matrix as the identity matrix – add a zero to the end of every row,
   and add a new row with a 1 and the rest 0s.-/
def ext {γ δ} (Ξ: matrix γ δ) (A: tp):
  matrix (A::γ) (A::δ)
| _ (ZVar _ _) := identity (A::δ) A (ZVar _ A)
| B (SVar _ x) := ⟦0⬝A⟧::(Ξ B x)

@[unfold_] lemma ext_zvar {γ δ} {Ξ: matrix γ δ} {A: tp}
  : ext Ξ A _ (ZVar _ _) = identity (A::δ) A (ZVar _ _) := by refl

@[unfold_] lemma ext_svar {γ δ} {Ξ: matrix γ δ} {A B: tp} {x: γ ∋ B}
  : ext Ξ A _ (SVar _ x) = ⟦0⬝A⟧::(Ξ _ x) := by refl

namespace vmul

@[simp] lemma vmul_nil {δ} {Ξ: matrix [] δ}
  : context.nil ⊛ Ξ = 0 := by refl

@[unfold_] lemma vmul_cons {γ δ} {T: τ} {Γ: context γ} {π: mult} {Ξ: matrix (T::γ) δ}
  : ⟦π⬝T⟧::Γ ⊛ Ξ = (π • Ξ T (ZVar _ T)) + (Γ ⊛ (λ U x, Ξ U (SVar T x))) :=
    by refl

@[simp] lemma zero_vmul
  : ∀ {γ δ: precontext} (M: matrix γ δ),
    0 ⊛ M = 0 :=
begin
  intros,
  induction γ with T γ ih,
  { refl },
  { unfold has_zero.zero zeros,
    simp * with unfold_,
    show ((0: mult) • M T (ZVar γ T) + 0 ⊛ λ (U : tp) (x : γ ∋ U), M U (SVar T x)) = 0,
    simp * },
end

@[simp] lemma vmul_ext_zero
  : ∀ {γ δ} {Γ: context γ} {Ξ: matrix γ δ} {T: τ},
    Γ ⊛ (λ U x, ⟦0⬝T⟧::(Ξ U x)) = ⟦0⬝T⟧::(Γ ⊛ Ξ) :=
begin
  intros,
  induction Γ with γ' π T' Γ ih,
  { refl },
  { simp * with unfold_ },
end

@[simp] lemma one_vmul
  : ∀ {γ δ} {Ξ: matrix γ δ} {T: τ}
    (x: γ ∋ T),
    -------------------------------
    (identity γ T x) ⊛ Ξ = Ξ T x :=
begin
  intros,
  induction x with γ' T' δ' T'' U x' ih;
  { simp * with unfold_ },
end

@[simp] lemma vmul_one
  : ∀ {γ} (Γ: context γ),
    Γ ⊛ (identity γ) = Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { simp [*, vmul_ext_zero] with unfold_ },
end

lemma smul_vmul
  : ∀ {γ δ} {Γ: context γ} {Ξ: matrix γ δ} {π: mult},
    (π • Γ) ⊛ Ξ = π • (Γ ⊛ Ξ) :=
begin
  intros,
  induction Γ with γ' π' T Γ ih;
  { simp [*, context.mul_smul]
    with unfold_ sop_form },
end

@[sop_form] lemma vmul_right_distrib
  : ∀ {γ δ} {Γ₁ Γ₂: context γ} {Ξ: matrix γ δ},
    (Γ₁ + Γ₂) ⊛ Ξ = (Γ₁ ⊛ Ξ) + (Γ₂ ⊛ Ξ) :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁;
  { cases Γ₂,
    simp * with unfold_ sop_form },
end

end vmul
open vmul

end matrix
