import sesh.term
import sesh.eval

open matrix
open term
open debrujin_idx


inductive thread_flag: Type
| Main: thread_flag
| Child: thread_flag

namespace thread_flag

inductive add: thread_flag → thread_flag → thread_flag → Prop
| CC: add Child Child Child
| CM: add Child Main Main
| MC: add Main Child Main

lemma child_add: ∀ {Φ}, add Child Φ Φ
| Child := add.CC
| Main := add.CM

lemma add_child: ∀ {Φ}, add Φ Child Φ
| Child := add.CC
| Main := add.MC

end thread_flag
open thread_flag

/- A tactic that can solve most goals involving thread flags. -/
meta def solve_flag: tactic unit :=
  `[ exact add.CC <|> exact add.CM <|> exact add.MC
     <|> assumption <|> exact child_add <|> exact add_child
     <|> tactic.fail "Failed to solve flags goal." ]

/- The type of parallel configurations. Configurations have rules
   for well-formedness (called "typing" in the paper). These are
   enforced by the Lean (config) Type. -/
inductive config: Π {γ}, context γ → thread_flag → Type
| CNu:
  Π {γ} {Γ: context γ} {Φ: thread_flag} {S: sesh_tp},
  /- Channel names, being treated the same as standard variables,
     are added to the usual typing context. -/
  config (⟦1⬝S♯⟧::Γ) Φ
  --------------------
→ config Γ Φ

/- Inherently typed config is problematic due to the existence
   of two derivations for a parallel composition. .. but could
   work if (dual S♯) = S♯ -/
| CComp:
  Π {γ} {Γ₁ Γ₂: context γ} {Φ₁ Φ₂: thread_flag} {S: sesh_tp}
  (Γ: context (S♯::γ))
  (Φ: thread_flag)
  (C: config (⟦1⬝S⟧::Γ₁) Φ₁)
  (D: config (⟦1⬝(sesh_tp.dual S)⟧::Γ₂) Φ₂)
  /- The same auto_param technique is used for the resulting
     context and thread flag. -/
  (_: auto_param (Γ = (⟦1⬝S♯⟧::(Γ₁ + Γ₂))) ``solve_context)
  (_: auto_param (add Φ₁ Φ₂ Φ) ``solve_flag),
  ----------
  config Γ Φ

| CMain:
  Π {γ} {Γ: context γ} {A: tp},
  term Γ A
  -------------
→ config Γ Main

| CChild:
  Π {γ} {Γ: context γ},
  term Γ End!
  --------------
→ config Γ Child
open config

notation `●`C:90 := CMain C
notation `○`C:90 := CChild C

/- thread evaluation contexts -/
@[reducible]
def thread_ctx_fn {γ} (Γₑ: context γ) (A': tp) (Φ: thread_flag) :=
  Π (Γ: context γ), term Γ A' → config (Γ + Γₑ) Φ

namespace thread_ctx_fn

@[reducible]
def apply {γ} {Γₑ Γ': context γ} {A': tp} {Φ: thread_flag}
  (f: thread_ctx_fn Γₑ A' Φ)
  (Γ: context γ)
  (M: term Γ' A')
  (h: auto_param (Γ = Γ'+Γₑ) ``solve_context)
  : config Γ Φ :=
cast (by solve_context) $ f Γ' M

end thread_ctx_fn

inductive thread_ctx
  : Π {γ} {A': tp} {Φ: thread_flag} (Γₑ: context γ),
    thread_ctx_fn Γₑ A' Φ → Type
| FMain:
  ∀ {γ} {Γₑ: context γ} {A' A: tp}
  (E: eval_ctx' Γₑ A' A),
  --------------------------------------
  thread_ctx Γₑ (λ Γ M, ●(E.f Γ M))

| FChild:
  ∀ {γ} {Γₑ: context γ} {A': tp}
  (E: eval_ctx' Γₑ A' End!),
  --------------------------------------
  thread_ctx Γₑ (λ Γ M, ○(E.f Γ M))

namespace thread_ctx

def ext:
  Π {γ δ: precontext} {Γ: context γ} {A': tp} {Φ: thread_flag}
    {F: thread_ctx_fn Γ A' Φ}
  (ρ: ren_fn γ δ),
  thread_ctx Γ F
→ let Γ' := (Γ ⊛ (λ B x, identity δ B $ ρ B x)) in
  Σ F': thread_ctx_fn Γ' A' Φ,
    thread_ctx Γ' F'
| _ _ _ _ _ _ ρ (FMain E) := ⟨_, FMain $ eval_ctx'.ext ρ E⟩
| _ _ _ _ _ _ ρ (FChild E) := ⟨_, FChild $ eval_ctx'.ext ρ E⟩

end thread_ctx

structure thread_ctx' {γ} (Γₑ: context γ) (A': tp) (Φ: thread_flag) :=
(f: thread_ctx_fn Γₑ A' Φ)
(h: thread_ctx Γₑ f)

namespace thread_ctx'

def ext {γ δ: precontext} {Γ: context γ} {A': tp} {Φ: thread_flag}
  (ρ: ren_fn γ δ)
  (F: thread_ctx' Γ A' Φ)
  : thread_ctx' (Γ ⊛ (λ B x, identity δ B $ ρ B x)) A' Φ
:= ⟨_, (thread_ctx.ext ρ F.h).snd⟩

end thread_ctx'

inductive context_reduces: ∀ {γ γ'}, context γ → context γ' → Prop
| ΓId:
  ∀ {γ} {Γ: context γ},
  context_reduces Γ Γ

| ΓSend:
    ∀ {γ} {Γ: context γ} {π: mult}
      {A: tp} {S: sesh_tp},
    context_reduces (⟦π⬝(!A⬝S)♯⟧::Γ) (⟦π⬝S♯⟧::Γ)

| ΓRecv:
    ∀ {γ} {Γ: context γ} {π: mult}
      {A: tp} {S: sesh_tp},
    context_reduces (⟦π⬝(?A⬝S)♯⟧::Γ) (⟦π⬝S♯⟧::Γ)

/- An experimental rule to allow self-duality of channel types.
   Never actually used. -/
| ΓHash:
    ∀ {γ} {Γ: context γ} {π: mult} {S: sesh_tp},
    context_reduces (⟦π⬝S♯⟧::Γ) (⟦π⬝(sesh_tp.dual S)♯⟧::Γ)
open context_reduces

inductive config_reduces
  : ∀ {γ γ'} {Γ: context γ} {Γ': context γ'} {Φ},
  context_reduces Γ Γ' → config Γ Φ → config Γ' Φ → Prop
notation C` -`h`⟶C `C':55 := config_reduces h C C'
| CEvalNu:
  ∀ {γ} {Γ: context γ} {S: sesh_tp} {Φ: thread_flag}
    {C C': config (⟦1⬝S♯⟧::Γ) Φ},
  C -ΓId⟶C C'
  ---------------------
→ ((CNu C) -ΓId⟶C (CNu C'))

/- TODO the right version results from commutativity.. somehow -/
| CEvalComp:
  ∀ {γ} {Γ₁ Γ₂: context γ} {S: sesh_tp} {Φ₁ Φ₂: thread_flag}
    {C C': config (⟦1⬝S⟧::Γ₁) Φ₁}
  (Γ: context $ S♯::γ)
  (hΓ: Γ = ⟦1⬝S♯⟧::(Γ₁ + Γ₂))
  (Φ: thread_flag)
  (hΦ: add Φ₁ Φ₂ Φ)
  (D: config (⟦1⬝sesh_tp.dual S⟧::Γ₂) Φ₂),
  C -ΓId⟶C C'
  ----------------------------------------------------------
→ ((CComp Γ Φ C D) -ΓId⟶C (CComp Γ Φ C' D))

| CEvalChild:
  ∀ {γ} {Γ: context γ}
    {M M': term Γ End!},
  M ⟶M M'
  -------------------------------
→ (○M -ΓId⟶C ○M)

| CEvalMain:
  ∀ {γ} {Γ: context γ} {A: tp}
    {M M': term Γ A},
  M ⟶M M'
  --------------------------------
→ (●M -ΓId⟶C ●M')

| CEvalFork:
  ∀ {γ} {Γₑ: context γ} {S: sesh_tp} {Φ}
  (F: thread_ctx' Γₑ (sesh_tp.dual S) Φ)
  (M: term (⟦1⬝S⟧::(0: context γ)) End!),
  ---------------------------------------
  ((F.f.apply Γₑ $ Fork $ Abs M)
  -ΓId⟶C
  (CNu
    $ CComp (⟦1⬝S♯⟧::Γₑ) Φ
      (CChild M)
      $ (F.ext $ ren_fn.lift_once $ sesh_tp.dual S).f.apply
        (⟦1⬝sesh_tp.dual S⟧::Γₑ)
        (Var
          (⟦1⬝sesh_tp.dual S⟧::0)
          $ ZVar _ $ sesh_tp.dual S)
        $ by solve_context))

| CEvalComm:
  ∀ {γ} {Γv: context γ} {A: tp} {S: sesh_tp}
    {Φ₁ Φ₂: thread_flag}
  (V: term Γv A)
  (hV: value V)
  (Φ: thread_flag)
  (hΦ: add Φ₁ Φ₂ Φ)
  (F: thread_ctx' (0: context γ) S Φ₁)
  (F': thread_ctx' (0: context γ) (tp.prod A $ sesh_tp.dual S) Φ₂),
  -----------------------------------------------------------------
  ((CComp (⟦1⬝(!A⬝S)♯⟧::Γv) Φ
    ((F.ext $ ren_fn.lift_once $ !A⬝S).f.apply
      (⟦1⬝!A⬝S⟧::Γv)
      (Send
        (⟦1⬝(!A⬝S)⟧::Γv)
        (term.rename (ren_fn.lift_once $ !A⬝S) _ V)
        (Var
          (⟦1⬝(!A⬝S)⟧::0)
          $ ZVar γ $ !A⬝S)
        $ by solve_context)
      $ by solve_context)
    $ (F'.ext $ ren_fn.lift_once $ sesh_tp.dual $ !A⬝S).f.apply
      (⟦1⬝sesh_tp.dual (!A⬝S)⟧::0)
      (Recv $
        Var
          (⟦1⬝sesh_tp.dual (!A⬝S)⟧::0)
          (begin convert
            (ZVar γ $ sesh_tp.dual $ !A⬝S),
            rw [sesh_tp.dual],
          end)
        $ begin
          simp [*, identity] with unfold_,
          h_generalize Hx: (ZVar γ $ sesh_tp.dual $ !A⬝S) == x,
          apply eq_of_heq, lmao
        end))
  -ΓSend⟶C
  (CComp (⟦1⬝S♯⟧::Γv) Φ
    ((F.ext $ ren_fn.lift_once S).f.apply
      (⟦1⬝S⟧::0)
      (Var
        (⟦1⬝S⟧::0)
        (ZVar γ S))
      $ by solve_context) -- now all the context used by V in thread 1 is being used by V
                          -- in thread 2. So the evaluation context must've _not_ used anything
                          -- really and must've been extended with the _entire_ context of V
    $ (F'.ext $ ren_fn.lift_once $ sesh_tp.dual S).f.apply
      (⟦1⬝sesh_tp.dual S⟧::Γv)
      $ Pair
        (⟦1⬝sesh_tp.dual S⟧::Γv)
        (term.rename (ren_fn.lift_once $ sesh_tp.dual S) _ V)
        (Var
          (⟦1⬝sesh_tp.dual S⟧::0)
          $ ZVar γ $ sesh_tp.dual S)
        $ by solve_context))

| CEvalWait:
  ∀ {γ} {Φ}
  (F: thread_ctx' (0: context γ) tp.unit Φ),
  ------------------------------------------
  ((CNu
    $ CComp (⟦1⬝End?♯⟧::0) Φ
      ((F.ext $ ren_fn.lift_once $ End?).f.apply
        (⟦1⬝End?⟧::0)
        (Wait
          $ Var
            (⟦1⬝End?⟧::0)
            $ ZVar γ End?)
        $ by solve_context)
      $ CChild
        $ Var (⟦1⬝End!⟧::0)
          (ZVar γ $ sesh_tp.dual End?)
          $ begin
            show ⟦1⬝End!⟧::0 = identity (End!::γ) End! (ZVar γ End!),
            simp with unfold_,
          end)
  -ΓId⟶C
  (F.f.apply (0: context γ) $ Unit 0))
