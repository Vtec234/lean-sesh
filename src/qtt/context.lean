/- Introduces typing contexts, which are lists of assumptions with associated
   multiplicities from an arbitrary semiring. -/

import tactic.ring
import tactic.abel
import algebra

import metastuff


/- In the QTT paper, this would be a "pre-precontext". -/
@[reducible]
def precontext (τ: Type) := list τ

/- In the QTT paper, this is the "precontext".
   τ is the Lean Type representing types of the embedded language.
   mult is the Lean Type representing elements of an arbitrary semiring,
   which describe the multiplicity of resources (how many times a resource
   can or will be used). -/
inductive context {τ mult: Type}: precontext τ → Type
| nil: context []
-- "You have a dependent pi (n) after a recursive arg (_ : context ns)
-- and Lean doesn't like this."
| cons {γ: precontext τ} (π: mult) (T: τ): context γ → context (T::γ)

notation `⟦`π`⬝`T`⟧::`Γ:90 := context.cons π T Γ

/- Indexes an assumption in the typing context. -/
inductive debrujin_idx {τ: Type}: precontext τ → τ → Type
infix ` ∋ `:55 := debrujin_idx
| ZVar: Π {γ: precontext τ} {T: τ},
  ----------
  (T::γ) ∋ T
| SVar: Π {γ: precontext τ} {T U: τ},
  γ ∋ T
  ----------
→ (U::γ) ∋ T
infix ` ∋ `:55 := debrujin_idx

namespace context

variable {τ: Type}
variables {mult: Type} [semiring mult]

def zeros: Π (γ: precontext τ), @context τ mult γ
| [] := nil
| (T::δ) := ⟦0⬝T⟧::(zeros δ)

instance {γ: precontext τ} : has_zero (@context τ mult γ) :=
  ⟨zeros γ⟩

@[unfold_] lemma zeros_cons {γ: precontext τ} {T: τ}
  : (0: @context τ mult (T::γ)) = ⟦(0: mult)⬝T⟧::(0: @context τ mult γ) := by refl

protected def add: Π {γ}, @context τ mult γ → @context τ mult γ → @context τ mult γ
| _ nil nil := nil
| _ (⟦π₁⬝T⟧::Γ₁) (⟦π₂⬝.(T)⟧::Γ₂) := ⟦(π₁+π₂)⬝T⟧::(add Γ₁ Γ₂)

instance {γ: precontext τ} : has_add (@context τ mult γ) :=
  ⟨context.add⟩

@[simp] lemma add_nil
  : (nil: @context τ mult []) + nil = nil := by refl

@[unfold_] lemma add_cons {γ} {Γ₁ Γ₂: @context τ mult γ} {π₁ π₂: mult} {T: τ}
  : ⟦π₁⬝T⟧::Γ₁ + ⟦π₂⬝T⟧::Γ₂ = ⟦(π₁+π₂)⬝T⟧::(Γ₁ + Γ₂) := by refl

/- addition makes a commutative monoid -/

@[simp] lemma zero_add
  : ∀ {γ} {Γ: @context τ mult γ},
    0 + Γ = Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { unfold has_zero.zero zeros at *,
    simp * with unfold_, show π+0=π,
    abel },
end

@[simp] lemma add_zero
  : ∀ {γ} {Γ: @context τ mult γ},
    Γ + 0 = Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { unfold has_zero.zero zeros at *,
    simp * with unfold_, show π+0=π,
    abel },
end

lemma add_comm
  : ∀ {γ} {Γ₁ Γ₂: @context τ mult γ},
    Γ₁ + Γ₂ = Γ₂ + Γ₁ :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁,
  { cases Γ₂, refl },
  { cases Γ₂ with _ π₂,
    simp * with unfold_ },
end

lemma add_assoc
  : ∀ {γ} {Γ₁ Γ₂ Γ₃: @context τ mult γ},
    (Γ₁ + Γ₂) + Γ₃ = Γ₁ + (Γ₂ + Γ₃) :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁,
  { cases Γ₂, cases Γ₃, refl },
  { cases Γ₂ with _ π₂,
    cases Γ₃ with _ π₃,
    simp * with unfold_ },
end

instance [h: semiring mult] {γ: precontext τ} : add_comm_monoid (@context τ mult γ) :=
{ add := context.add,
  zero := zeros γ,
  zero_add := @zero_add τ mult h γ,
  add_zero := @add_zero τ mult h γ,
  add_comm := @add_comm τ mult h γ,
  add_assoc := @add_assoc τ mult h γ }

protected def smul: Π {γ}, mult → @context τ mult γ → @context τ mult γ
| _ π nil := nil
| _ π (⟦π'⬝T⟧::Γ) := ⟦(π*π')⬝T⟧::(smul π Γ)

instance {γ: precontext τ} : has_scalar mult (@context τ mult γ) :=
  ⟨context.smul⟩

@[simp] lemma smul_nil {π: mult}
  : π • (nil: @context τ mult []) = nil := by refl

@[unfold_] lemma smul_cons {γ} {Γ: @context τ mult γ} {π π': mult} {T: τ}
  : π • ⟦π'⬝T⟧::Γ = ⟦(π*π')⬝T⟧::(π • Γ) := by refl

/- scalar multiplication (mult • context) makes a semimodule -/

@[simp] lemma one_smul
  : ∀ {γ} {Γ: @context τ mult γ},
    ((1: mult) • Γ: @context τ mult γ) = Γ :=
begin
  intros,
  induction Γ with γ π T Δ ih,
  { refl },
  { simp * with unfold_ },
end

@[simp] lemma zero_smul
  : ∀ {γ} {Γ: @context τ mult γ},
    ((0: mult) • Γ: @context τ mult γ) = 0 :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { simp * with unfold_ },
end

@[simp] lemma smul_zero
  : ∀ {γ} {π: mult},
    (π • 0: @context τ mult γ) = 0 :=
begin
  intros,
  induction γ with T γ ih,
  { refl },
  { unfold has_zero.zero zeros,
    unfold has_zero.zero zeros at ih,
    simp * with unfold_,
    show π*0=0, simp * },
end

@[sop_form] lemma smul_add
  : ∀ {γ} {π: mult} {Γ₁ Γ₂: @context τ mult γ},
    π • (Γ₁ + Γ₂) = π•Γ₁ + π•Γ₂ :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁,
  { cases Γ₂, refl },
  { cases Γ₂ with _ π₂,
    simp [*, left_distrib] with unfold_ },
end

@[sop_form] lemma add_smul
  : ∀ {γ} {π₁ π₂: mult} {Γ: @context τ mult γ},
    (π₁ + π₂) • Γ = π₁•Γ + π₂•Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { simp [*, right_distrib] with unfold_ },
end

lemma mul_smul
  : ∀ {γ} {π π': mult} {Γ: @context τ mult γ},
    (π * π') • Γ = π • (π' • Γ) :=
begin
  intros, induction Γ with γ π T Γ ih,
  { refl },
  { simp [*, mul_assoc] with unfold_ },
end

instance [h: semiring mult] {γ: precontext τ} : semimodule mult (@context τ mult γ) :=
{ one_smul := @one_smul τ mult h γ,
  zero_smul := @zero_smul τ mult h γ,
  smul_zero := @smul_zero τ mult h γ,
  smul_add := @smul_add τ mult h γ,
  add_smul := @add_smul τ mult h γ,
  mul_smul := @mul_smul τ mult h γ }

end context
