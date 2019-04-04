/- Introduces types of Synchronous GV. -/

import metastuff


mutual inductive tp, sesh_tp
/- A, B, C -/
with tp: Type
| unit: tp
| fn: tp → tp → tp /- A⊸B -/
| sum: tp → tp → tp /- A+B -/
| prod: tp → tp → tp /- AxB -/
| sesh: sesh_tp → tp /- S -/
| hash: sesh_tp → tp /- S♯ -/
/- S, T -/
with sesh_tp: Type
| send: tp → sesh_tp → sesh_tp /- !A.S -/
| recv: tp → sesh_tp → sesh_tp /- ?A.S -/
| end_send: sesh_tp /- End! -/
| end_recv: sesh_tp /- End? -/

infix `⊸`:90 := tp.fn
notation S`♯`:90 := tp.hash S
notation `End!` := sesh_tp.end_send
notation `End?` := sesh_tp.end_recv
notation `!`A`⬝`S:90 := sesh_tp.send A S
notation `?`A`⬝`S:90 := sesh_tp.recv A S

/- Automatically coerce session types to types. -/
instance sesh_tp_to_tp : has_coe sesh_tp tp :=
  ⟨λ S, tp.sesh S⟩

namespace sesh_tp

-- TODO perhaps this should be an inductive relation.
def dual: sesh_tp → sesh_tp
| !A⬝S := ?A⬝(dual S)
| ?A⬝S := !A⬝(dual S)
| End! := End?
| End? := End!

lemma dual_dual (S: sesh_tp)
  : dual (dual S) = S :=
begin
  induction S with _ _ ih _ _ ih ih ih;
  unfold dual;
  rw [ih]
end

@[simp] lemma dual_end_send: dual End! = End? := by refl
@[simp] lemma dual_end_recv: dual End? = End! := by refl

-- dual S♯ = S♯ should work as an axiom to remove both connects
-- could be added to the session type/environment reduction -> this might break associativity proof
-- but could be better if added as a separate relation -~~>

end sesh_tp
