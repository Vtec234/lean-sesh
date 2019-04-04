/- Introduces renaming and substitution on terms and values. -/
import sesh.term


/- The type of renaming functions which transport indices
   from one precontext to another. -/
def ren_fn (γ δ) := Π (A: tp), γ ∋ A → δ ∋ A

namespace ren_fn
open debrujin_idx

/- A renaming function which moves every index/variable up once. -/
@[reducible]
def lift_once {γ: precontext} (B: tp): ren_fn γ (B::γ) := (λ A, @SVar γ A B)

@[reducible]
def lift_over (γ: precontext) (A B: tp): ren_fn (A::γ) (A::B::γ)
| _ (ZVar _ _) := ZVar _ _
| _ (SVar _ x) := SVar _ (SVar _ x)

@[reducible]
def lift_over_two (γ: precontext) (A B C: tp): ren_fn (A::B::γ) (A::B::C::γ)
| _ (ZVar _ _) := ZVar _ _
| _ (SVar _ (ZVar _ _)) := SVar _ (ZVar _ _)
| _ (SVar _ (SVar _ x)) := SVar _ (SVar _ (SVar _ x))

/- The extended ren_fn is identical, but has an extended precontext in the type. -/
def ext {γ δ} (ρ: ren_fn γ δ) (A: tp): ren_fn (A::γ) (A::δ)
| _ (ZVar _ B) := (ZVar _ B)
| B (SVar C x) := SVar C (ρ B x)

@[simp] lemma ext_zvar {γ δ} {ρ: ren_fn γ δ} {A: tp}
  : ext ρ A _ (ZVar _ A) = (ZVar _ A) := by refl

@[unfold_] lemma ext_svar {γ δ} {ρ: ren_fn γ δ} {A B: tp} {x: γ ∋ B}
  : ext ρ A B (SVar A x) = SVar A (ρ B x) := by refl

end ren_fn

namespace term

/- Applies the renaming ρ to a term M. The resulting term
   is the same one and has the same type, but its context
   is Γ times the identity matrix. This has the effect of
   simply appending one or more zero-resourced bindings to
   Γ, and since we treat those as non-existent, the context
   is essentially the same. -/
def rename: Π {γ δ: precontext} {Γ: context γ} {A: tp}
  (ρ: ren_fn γ δ)
  (Δ: context δ)
  (M: term Γ A)
  (h: auto_param (Δ = Γ ⊛ (λ B x, matrix.identity δ B $ ρ B x)) ``solve_context),
  term Δ A
/- In most cases we have to carry through a proof
   that the context of the resulting term is the right
   one. In cases where variable bindings are introduced,
   the body under the binder also has to be `convert`ed
   by constructing a proof that the lifted context is still
   the right one. -/
| _ _ _ _ ρ _ (Var Γ x _) h  := Var _ (ρ _ x)
| _ _ _ _ ρ _ (Abs e) h := Abs (rename (ρ.ext _) _ e)
| _ _ _ _ ρ _ (App _ M N _) h := App _ (rename ρ _ M) (rename ρ _ N)
| _ _ _ _ _ _ (Unit _ _) h := Unit _
| _ _ _ _ ρ _ (LetUnit _ M N _) h := LetUnit _ (rename ρ _ M) (rename ρ _ N)
| _ _ _ _ ρ _ (Pair _ M N _) h := Pair _ (rename ρ _ M) (rename ρ _ N)
| _ δ _ _ ρ _ (LetPair Γ M N _) h := LetPair
  _
  (rename ρ _ M)
  (rename ((ρ.ext _).ext _) _ N)
| _ δ _ _ ρ _ (Case Γ L M N _) h := Case
  _
  (rename ρ _ L)
  (rename (ρ.ext _) _ M)
  (rename (ρ.ext _) _ N)
| _ _ _ _ ρ _ (Send _ M N _) h := Send _ (rename ρ _ M) (rename ρ _ N)
| _ _ _ _ ρ _ (Inl B e) h := Inl B (rename ρ _ e)
| _ _ _ _ ρ _ (Inr A e) h := Inr A (rename ρ _ e)
| _ _ _ _ ρ _ (Fork e) h := Fork (rename ρ _ e)
| _ _ _ _ ρ _ (Recv e) h := Recv (rename ρ _ e)
| _ _ _ _ ρ _ (Wait e) h := Wait (rename ρ _ e)

def lift_once {γ: precontext} {Γ: context γ} {A: tp}
  (M: term Γ A)
  (B: tp)
  : term (⟦0⬝B⟧::Γ) A :=
rename (ren_fn.lift_once B) _ M

end term

namespace value

lemma rename:
  ∀ {γ δ}
    {Γ: context γ} {A: tp}
    {V: term Γ A}
  (h: value V)
  (ρ: ren_fn γ δ),
  value (term.rename ρ _ V (by solve_context))
| _ _ _ _ _ (VVar _ x _) ρ := VVar _ (ρ _ x)
| _ _ _ _ _ (VAbs M) ρ :=
  VAbs $ term.rename (ρ.ext _) _ M
| _ _ _ _ _ (VUnit _ _) ρ := VUnit _
| _ _ _ _ _ (VPair _ _ hM hN) ρ :=
  VPair
    _ (by solve_context)
    (hM.rename ρ)
    (hN.rename ρ)
| _ _ _ _ _ (VInl B hM) ρ := VInl B (hM.rename ρ)
| _ _ _ _ _ (VInr B hM) ρ := VInr B (hM.rename ρ)

end value

/- For every variable x in γ, (σ _ x) where (σ: sub_fn Ξ) returns
   the term which should be substituted into that variable. The
   resource requirements of that term can be extracted out of
   the matrix Ξ. -/
def sub_fn {γ δ} (Ξ: matrix γ δ) :=
  Π (A: tp) (x: γ ∋ A), term (Ξ A x) A

namespace sub_fn
open debrujin_idx
open term

/- Extends the substitution given by Ξ into one over contexts extended with T. -/
def ext {γ δ} {Ξ: matrix γ δ} (σ: sub_fn Ξ) (A: tp)
  : sub_fn (Ξ.ext A)
| _ (ZVar _ A) := Var _ (ZVar _ A)
| B (SVar _ x) := rename (ren_fn.lift_once A) _ (σ B x)

end sub_fn

namespace term
open debrujin_idx

/- Applies simultaneous substitution, replacing all variables
   in a term with whatever the matrix Ξ contains. -/
def subst
  : Π {γ δ} {Γ: context γ} {Ξ: matrix γ δ} {A}
    (σ: sub_fn Ξ)
    (Δ: context δ)
    (M: term Γ A)
    (h: auto_param (Δ = Γ ⊛ Ξ) ``solve_context),
    term Δ A
| _ _ _ _ _ σ _ (Var _ x _) _ := cast (by solve_context) $ σ _ x
| _ _ _ _ _ σ _ (Abs M) _ := Abs $ subst (σ.ext _) _ M
| _ _ _ _ _ σ _ (App _ M N _) _ := App _ (subst σ _ M) (subst σ _ N)
| _ _ _ _ _ σ _ (Unit _ _) _ := Unit _
| _ _ _ _ _ σ _ (LetUnit _ M N _) _ := LetUnit _ (subst σ _ M) (subst σ _ N)
| _ _ _ _ _ σ _ (Pair _ M N _) _ := Pair _ (subst σ _ M) (subst σ _ N)
| _ _ Γ Ξ _ σ _ (LetPair _ M N _) _ :=
  LetPair
    _
    (subst σ _ M)
    (subst ((σ.ext _).ext _) _ N)
| _ _ _ _ _ σ _ (Case _ L M N _) _ := Case
  _
  (subst σ _ L)
  (subst (σ.ext _) _ M)
  (subst (σ.ext _) _ N)
| _ _ _ _ _ σ _ (Send _ M N _) _ := Send _ (subst σ _ M) (subst σ _ N)
| _ _ _ _ _ σ _ (Inl B M) _ := Inl B (subst σ _ M)
| _ _ _ _ _ σ _ (Inr A M) _ := Inr A (subst σ _ M)
| _ _ _ _ _ σ _ (Fork M) _ := Fork (subst σ _ M)
| _ _ _ _ _ σ _ (Recv M) _ := Recv (subst σ _ M)
| _ _ _ _ _ σ _ (Wait M) _ := Wait (subst σ _ M)

def ssub_mat {γ} (Γ: context γ) (A: tp)
  : matrix (A::γ) γ
| _ (ZVar _ _) := Γ
| B (SVar _ x) := matrix.identity γ B x

def ssub_sub {γ} {A: tp} (Γ: context γ) (M: term Γ A)
  : sub_fn (ssub_mat Γ A)
| _ (ZVar _ _) := M
| _ (SVar _ x) := Var _ x (begin unfold ssub_mat, simp end)

def ssubst {γ} {Γ Γ': context γ} {A B: tp} {π: mult}
  (Δ: context γ)
  (e: term (⟦π⬝B⟧::Γ) A) -- The term being sub'd into requires π Bs
  (s: term Γ' B) -- The sub'd term requires Γ'
  (_: auto_param (Δ = Γ + π•Γ') ``solve_context)
  -------------------
  : term Δ A := subst (ssub_sub Γ' s) _ e
  (begin
    simp with unfold_, unfold ssub_mat, solve_context,
  end)

/-
def dsub_mat {γ} (Γ: context γ) (A B: tp)
  : matrix (A::B::γ) γ := sorry

def dsub_sub {γ} {A B: tp} (Γ: context γ) (M: term Γ A) (N: term Γ B)
  : sub_fn (dsub_mat Γ A B)
| _ ZVar := M
| _ (SVar x) := Var x
-/

def dsubst {γ} {Γ Γ₁ Γ₂: context γ} {A B₁ B₂: tp} {π₁ π₂: mult}
  (Δ: context γ)
  (e: term (⟦π₁⬝B₁⟧::⟦π₂⬝B₂⟧::Γ) A)
  (s₁: term Γ₁ B₁)
  (s₂: term Γ₂ B₂)
  (_: auto_param (Δ = Γ + π₁•Γ₁ + π₂•Γ₂) ``solve_context)
  ----------------
  : term Δ A :=
    sorry

end term

