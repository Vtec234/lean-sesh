/- Introduces typing contexts, which are lists of assumptions with associated
   multiplicities from an arbitrary semiring. -/

import tactic.ring
import tactic.abel
import algebra

import metastuff
import sesh.types
import sesh.mult


/- In the QTT paper, this would be a "pre-precontext". -/
@[reducible]
def precontext := list tp

/- In the QTT paper, this is the "precontext".
   τ is the Lean Type representing types of the embedded language.
   mult is the Lean Type representing elements of an arbitrary semiring,
   which describe the multiplicity of resources (how many times a resource
   can or will be used). -/
inductive context: precontext → Type
| nil: context []
-- "You have a dependent pi (n) after a recursive arg (_ : context ns)
-- and Lean doesn't like this."
| cons {γ: precontext} (π: mult) (T: tp): context γ → context (T::γ)
notation `⟦`π`⬝`T`⟧::`Γ:90 := context.cons π T Γ

/- Indexes a judgment in the typing context. Definition follows
   the inductive structure of natural numbers. -/
inductive debrujin_idx: precontext → tp → Type
infix ` ∋ `:55 := debrujin_idx
| ZVar: Π (γ: precontext) (T: tp),
  ----------
  (T::γ) ∋ T
| SVar: Π {γ: precontext} {T: tp} (U: tp),
  γ ∋ T
  ----------
→ (U::γ) ∋ T
infix ` ∋ `:55 := debrujin_idx

namespace context

-- An ugly hack which makes the contexts non-generic, but rather specific
-- to `tp`. Necessary because generic lemmas make `simp` slow to the point
-- of timing out and being generally unusable. This whole module should
-- still work when the variables are reintroduced.
--variable {τ: Type}
@[reducible]
def τ := tp
--variables {mult: Type} [semiring mult]

def zeros: Π (γ: precontext), context γ
| [] := nil
| (T::δ) := ⟦0⬝T⟧::(zeros δ)

instance {γ: precontext} : has_zero (context γ) :=
  ⟨zeros γ⟩

@[unfold_] lemma zeros_nil
  : (0: context []) = nil := by refl

@[unfold_] lemma zeros_cons {γ: precontext} {T: τ}
  : (0: context (T::γ)) = ⟦(0: mult)⬝T⟧::(0: context γ) := by refl

protected def add: Π {γ}, context γ → context γ → context γ
| _ nil nil := nil
| _ (⟦π₁⬝T⟧::Γ₁) (⟦π₂⬝.(T)⟧::Γ₂) := ⟦(π₁+π₂)⬝T⟧::(add Γ₁ Γ₂)

instance {γ: precontext} : has_add (context γ) :=
  ⟨context.add⟩

@[simp] lemma add_nil
  : (nil: context []) + nil = nil := by refl

@[unfold_] lemma add_cons {γ} {Γ₁ Γ₂: context γ} {π₁ π₂: mult} {T: τ}
  : ⟦π₁⬝T⟧::Γ₁ + ⟦π₂⬝T⟧::Γ₂ = ⟦(π₁+π₂)⬝T⟧::(Γ₁ + Γ₂) := by refl

/- addition makes a commutative monoid -/

@[simp] lemma zero_add
  : ∀ {γ} {Γ: context γ},
    0 + Γ = Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { unfold has_zero.zero zeros at *,
    simp * with unfold_, show 0+π=π,
    abel },
end

@[simp] lemma add_zero
  : ∀ {γ} {Γ: context γ},
    Γ + 0 = Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { unfold has_zero.zero zeros at *,
    simp * with unfold_, show 0+π=π,
    abel },
end

lemma zeros_left {γ} {Γ₁ Γ₂: context γ}
  (h: Γ₁ + Γ₂ = 0)
  : Γ₁ = 0 :=
begin
  induction Γ₁ with γ π T Γ ih,
  { unfold has_zero.zero zeros },
  { cases Γ₂ with _ π₂ _ Γ₂,
    unfold has_zero.zero zeros at h,
    rw [add_cons] at h, simp at h,
    congr' 1,
    { exact mult.zeros_left h.left },
    { exact ih h.right },
  }
end

lemma zeros_right {γ} {Γ₁ Γ₂: context γ}
  (h: Γ₁ + Γ₂ = 0)
  : Γ₂ = 0 :=
begin
  induction Γ₂ with γ π T Γ ih,
  { unfold has_zero.zero zeros },
  { cases Γ₁ with _ π₁ _ Γ₁,
    unfold has_zero.zero zeros at h,
    rw [add_cons] at h, simp at h,
    congr' 1,
    { exact mult.zeros_left h.left },
    { exact ih h.right },
  }
end

lemma add_comm
  : ∀ {γ} {Γ₁ Γ₂: context γ},
    Γ₁ + Γ₂ = Γ₂ + Γ₁ :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁,
  { cases Γ₂, refl },
  { cases Γ₂ with _ π₂,
    simp * with unfold_ },
end

lemma add_assoc
  : ∀ {γ} {Γ₁ Γ₂ Γ₃: context γ},
    (Γ₁ + Γ₂) + Γ₃ = Γ₁ + (Γ₂ + Γ₃) :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁,
  { cases Γ₂, cases Γ₃, refl },
  { cases Γ₂ with _ π₂,
    cases Γ₃ with _ π₃,
    simp * with unfold_ },
end

instance {γ: precontext} : add_comm_monoid (context γ) :=
{ add := context.add,
  zero := zeros γ,
  zero_add := @zero_add γ,
  add_zero := @add_zero γ,
  add_comm := @add_comm γ,
  add_assoc := @add_assoc γ }

protected def smul: Π {γ}, mult → context γ → context γ
| _ π nil := nil
| _ π (⟦π'⬝T⟧::Γ) := ⟦(π*π')⬝T⟧::(smul π Γ)

instance {γ: precontext} : has_scalar mult (context γ) :=
  ⟨context.smul⟩

@[simp] lemma smul_nil {π: mult}
  : π • (nil: context []) = nil := by refl

@[unfold_] lemma smul_cons {γ} {Γ: context γ} {π π': mult} {T: τ}
  : π • ⟦π'⬝T⟧::Γ = ⟦(π*π')⬝T⟧::(π • Γ) := by refl

/- scalar multiplication (mult • context) makes a semimodule -/

@[simp] lemma one_smul
  : ∀ {γ} {Γ: context γ},
    ((1: mult) • Γ: context γ) = Γ :=
begin
  intros,
  induction Γ with γ π T Δ ih,
  { refl },
  { simp * with unfold_ },
end

@[simp] lemma zero_smul
  : ∀ {γ} {Γ: context γ},
    ((0: mult) • Γ: context γ) = 0 :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { simp * with unfold_ },
end

@[simp] lemma smul_zero
  : ∀ {γ} {π: mult},
    (π • 0: context γ) = 0 :=
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
  : ∀ {γ} {π: mult} {Γ₁ Γ₂: context γ},
    π • (Γ₁ + Γ₂) = π•Γ₁ + π•Γ₂ :=
begin
  intros,
  induction Γ₁ with γ₁ π₁ T₁ Γ₁ ih₁,
  { cases Γ₂, refl },
  { cases Γ₂ with _ π₂,
    simp [*, left_distrib] with unfold_ },
end

@[sop_form] lemma add_smul
  : ∀ {γ} {π₁ π₂: mult} {Γ: context γ},
    (π₁ + π₂) • Γ = π₁•Γ + π₂•Γ :=
begin
  intros,
  induction Γ with γ π T Γ ih,
  { refl },
  { simp [*, right_distrib] with unfold_ },
end

lemma mul_smul
  : ∀ {γ} {π π': mult} {Γ: context γ},
    (π * π') • Γ = π • (π' • Γ) :=
begin
  intros, induction Γ with γ π T Γ ih,
  { refl },
  { simp [*, mul_assoc] with unfold_ },
end

instance {γ: precontext} : semimodule mult (context γ) :=
{ one_smul := @one_smul γ,
  zero_smul := @zero_smul γ,
  smul_zero := @smul_zero γ,
  smul_add := @smul_add γ,
  add_smul := @add_smul γ,
  mul_smul := @mul_smul γ }

end context
