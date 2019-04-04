/- Introduces a commutative semiring of zero-one-many. -/

import metastuff


@[derive decidable_eq]
inductive mult: Type
/- Zero represents assumptions which cannot be computed with,
   but could be used for typing, were I to implement dependent
   types in the embedded language. Since I didn't, zero is basically
   useless. -/
| Zero: mult
/- A one-multiplicity assumption can be used once in computation,
   i.e is linear. -/
| One: mult
/- A many-multiplicity assumption is non-linear and can be used
   multiple times. -/
| Many: mult

notation `ω` := mult.Many

namespace mult

instance : has_zero mult :=
  ⟨mult.Zero⟩

instance : has_one mult :=
  ⟨mult.One⟩

protected def add: mult → mult → mult
| 0 π := π
| π 0 := π
| 1 1 := ω
| ω _ := ω
| _ ω := ω

instance : has_add mult :=
  ⟨mult.add⟩

/- addition makes a commutative monoid -/

@[simp] lemma zero_add (π: mult)
  : 0 + π = π := by { cases π; refl }

@[simp] lemma add_zero (π: mult)
  : π + 0 = π := by { cases π; refl }

lemma zeros_left {π₁ π₂: mult}
  (h: π₁ + π₂ = 0)
  : π₁ = 0 := begin
  cases π₁; cases π₂; cases h,
  refl
end

lemma zeros_right {π₁ π₂: mult}
  (h: π₁ + π₂ = 0)
  : π₂ = 0 :=
begin
  cases π₁; cases π₂; cases h,
  refl
end

lemma add_comm (π₁ π₂: mult)
  : π₁ + π₂ = π₂ + π₁ :=
by { cases π₁; cases π₂; refl }

lemma add_assoc (π₁ π₂ π₃: mult)
  : π₁ + π₂ + π₃ = π₁ + (π₂ + π₃) :=
by { cases π₁; cases π₂; cases π₃; refl }

instance : add_comm_monoid mult :=
{ add := mult.add,
  zero := mult.Zero,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  add_assoc := add_assoc }

protected def mul: mult → mult → mult
| _ 0 := 0
| 0 _ := 0
| π 1 := π
| _ ω := ω

instance : has_mul mult :=
  ⟨mult.mul⟩

/- multiplication makes a commutative monoid -/

@[simp] lemma one_mul (π: mult)
  : 1 * π = π := by { cases π; refl }

@[simp] lemma mul_one (π: mult)
  : π * 1 = π := by { cases π; refl }

lemma mul_comm (π₁ π₂: mult)
  : π₁ * π₂ = π₂ * π₁ :=
by { cases π₁; cases π₂; refl }

lemma mul_assoc (π₁ π₂ π₃: mult)
  : π₁ * π₂ * π₃ = π₁ * (π₂ * π₃) :=
by { cases π₁; cases π₂; cases π₃; refl }

instance : comm_monoid mult :=
{ mul := mult.mul,
  one := mult.One,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_comm := mul_comm,
  mul_assoc := mul_assoc }

/- mult with + and * makes a commutative semiring -/

@[simp] lemma zero_mul (π: mult)
  : 0 * π = 0 :=
by { cases π; refl }

@[simp] lemma mul_zero (π: mult)
  : π * 0 = 0 :=
by { cases π; refl }

@[sop_form] lemma left_distrib (π₁ π₂ π₃: mult)
  : π₁ * (π₂ + π₃) = π₁ * π₂ + π₁ * π₃ :=
by { cases π₁; cases π₂; cases π₃; refl }

@[sop_form] lemma right_distrib (π₁ π₂ π₃: mult)
  : (π₁ + π₂) * π₃ = π₁ * π₃ + π₂ * π₃ :=
by { cases π₁; cases π₂; cases π₃; refl }

instance : comm_semiring mult :=
{ zero_mul := zero_mul,
  mul_zero := mul_zero,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
  ..mult.add_comm_monoid,
  ..mult.comm_monoid }

end mult
