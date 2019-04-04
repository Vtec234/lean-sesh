import sesh.term
import sesh.eval
open term

inductive comms_construct: ∀ {γ} {Γ: context γ} {A: tp}, term Γ A → Prop
| CCFork:
  ∀ {γ} {Γ: context γ} {S: sesh_tp}
    {V: term Γ $ S⊸End!}
  (hV: value V),
  comms_construct (Fork V)

| CCSend:
  ∀ {γ} {Γ₁ Γ₂: context γ} {A: tp} {S: sesh_tp}
    {V: term Γ₁ A} {W: term Γ₂ $ !A⬝S}
  (Γ: context γ)
  (hV: value V)
  (hW: value W)
  (_: auto_param (Γ = Γ₁+Γ₂) ``solve_context),
  comms_construct (Send Γ V W)

| CCRecv:
  ∀ {γ} {Γ: context γ} {A: tp} {S: sesh_tp}
    {V: term Γ $ ?A⬝S}
  (hV: value V),
  comms_construct (Recv V)

| CCWait:
  ∀ {γ} {Γ: context γ}
    {V: term Γ End?}
  (hV: value V),
  comms_construct (Wait V)
open comms_construct

inductive comms_blocked {γ} {Γ: context γ} {A: tp} (M: term Γ A): Prop
| mk: ∀ {A': tp} {Γ' Γₑ: context γ} {N: term Γ' A'}
  (hN: comms_construct N)
  (E: eval_ctx' Γₑ A' A)
  (hΓ: Γ = Γ'+Γₑ)
  (h: M = E.f.apply Γ N),
  comms_blocked

namespace comms_blocked

/- Wraps a comms_blocked M in another evaluation context,
   returning comms_blocked E[M]. -/
def wrap {γ} {Γ Γₑ: context γ} {A' A: tp} {M: term Γ A'}
  (Γ': context γ)
  (hM: comms_blocked M)
  (E: eval_ctx' Γₑ A' A)
  (EM: term Γ' A)
  (hΓ': Γ' = Γ+Γₑ)
  (hEM: EM = E.f.apply Γ' M)
  : comms_blocked EM :=
match hM with
| (@mk _ _ _ _ _ _ _ N hN E₀ hΓ₀ h₀) :=
  ⟨hN, E₀.wrap E _ rfl, (begin simp [hΓ', hΓ₀] end),
   eval_ctx'.wrap_composes _ hΓ₀ M _ hΓ' EM h₀ hEM⟩
end

end comms_blocked

inductive progress {γ} {Γ: context γ} {A: tp} (M: term Γ A): Prop
| Done:
  value M
→ progress

| Step:
  ∀ (M': term Γ A),
  M ⟶M M'
→ progress

| Conc:
  comms_blocked M
→ progress

namespace progress
open value
open comms_construct
open eval_ctx
open term_reduces

set_option eqn_compiler.lemmas false
def mk_progress'
  : Π {γ: precontext} {A: tp}
  (Γ: context γ) (M: term Γ A)
  (hΓ: auto_param (Γ = 0) ``solve_context),
  progress M
/- Can't have variables in an empty context. -/
| _ _ _ (Var Γ x hΓ) hZero := begin
  exfalso,
  apply matrix.identity_neq_zero,
  simp [hΓ] at hZero, exact hZero,
end

/- Pure values. -/
| _ _ _ (Abs M) _ := Done $ VAbs M
| _ _ _ (Unit Γ _) _ := Done $ VUnit _

/- Slightly simpler cases. -/
| γ _ Γ (Inl B M) hΓ :=
  match mk_progress' Γ M with
  | Done M_val := Done
    $ VInl B M_val
  | Step M' M_step := Step
    (Inl B M')
    $ EvalLift Γ
      ⟨_, EInl B _ $ EHole γ _⟩
      (Inl B M) (Inl B M')
      (by rw [context.add_zero])
      M_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Inl B x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (Inl B x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ M_conc
      ⟨_, EInl B _ $ EHole γ _⟩
      (Inl B M)
      (by rw [context.add_zero])
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Inl B x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  end
| γ _ Γ (Inr A M) hΓ :=
  match mk_progress' Γ M with
  | Done M_val := Done
    $ VInr A M_val
  | Step M' M_step := Step
    (Inr A M')
    $ EvalLift Γ
      ⟨_, EInr A _ $ EHole γ _⟩
      (Inr A M) (Inr A M')
      (by rw [context.add_zero])
      M_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Inr A x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (Inr A x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ M_conc
      ⟨_, EInr A _ $ EHole γ _⟩
      (Inr A M)
      (by rw [context.add_zero])
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Inr A x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  end
| .(γ) _ .(Γ) (@Pair γ Γ₁ Γ₂ A B Γ M N hΓ) hZero :=
  have hZero: Γ₁ = 0 ∧ Γ₂ = 0, from begin
    simp at hΓ hZero ⊢, rw [hΓ] at hZero,
    exact ⟨context.zeros_left hZero, context.zeros_right hZero⟩,
  end,
  match mk_progress' Γ₁ M hZero.left with
  | Step M' M_step := Step
    (Pair Γ M' N)
    $ EvalLift Γ
      ⟨_, EPairLeft Γ₂ (by rw [context.zero_add]) N _ $ EHole γ A⟩
      (Pair Γ M N) (Pair Γ M' N) hΓ M_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Pair (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (Pair (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ M_conc
      ⟨_, EPairLeft Γ₂ (by rw [context.zero_add]) N _ $ EHole γ A⟩
      (Pair Γ M N) hΓ
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Pair (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Done M_val :=
    match mk_progress' Γ₂ N hZero.right with
    | Done N_val := Done
      $ VPair Γ hΓ M_val N_val
    | Step N' N_step := Step
      (Pair Γ M N')
      $ EvalLift Γ
        ⟨_, EPairRight Γ₁ (by rw [context.add_zero]) M_val _ $ EHole γ B⟩
        (Pair Γ M N) (Pair Γ M N')
        (by simp [hΓ])
        N_step
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Hx: N == x,
          h_generalize Hy: (Pair (Γ₂+Γ₁) M x) == y,
          apply eq_of_heq, apply heq.subst Hy,
          congr' 1; simp [hΓ, Hx]
        end)
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Hx: N' == x,
          h_generalize Hy: (Pair (Γ₂+Γ₁) M x) == y,
          apply eq_of_heq, apply heq.subst Hy,
          congr' 1; simp [hΓ, Hx]
        end)
    | Conc N_conc := Conc
      $ comms_blocked.wrap Γ N_conc
        ⟨_, EPairRight Γ₁ (by rw [context.add_zero]) M_val _ $ EHole γ B⟩
        (Pair Γ M N)
        (by simp [hΓ])
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Hx: N == x,
          h_generalize Hy: (Pair (Γ₂+Γ₁) M x) == y,
          apply eq_of_heq, apply heq.subst Hy,
          congr' 1; simp [hΓ, Hx]
        end)
    end
  end

/- Cases with special evaluation rules. -/
| .(γ) _ .(Γ) (@App γ Γ₁ Γ₂ A B Γ fn arg hΓ') hΓ :=
  have hΓ: Γ₁ = 0 ∧ Γ₂ = 0, from begin
    simp at hΓ hΓ' ⊢, rw [hΓ] at hΓ',
    exact ⟨context.zeros_left hΓ'.symm, context.zeros_right hΓ'.symm⟩
  end,
  match mk_progress' Γ₁ fn hΓ.left with
  | Step fn' fn_step := Step
    (App Γ fn' arg)
    $ EvalLift Γ
      ⟨_, EAppLeft Γ₂ (by rw [context.zero_add]) arg _ $ EHole γ $ A⊸B⟩
      (App Γ fn arg) (App Γ fn' arg)
      hΓ' fn_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hfn: fn == x,
        h_generalize Happ: (App (Γ₁ + Γ₂) x arg) == y,
        apply eq_of_heq, apply heq.subst Happ,
        congr' 1; simp [hΓ', Hfn]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hfn': fn' == x,
        h_generalize Happ: (App (Γ₁ + Γ₂) x arg) == y,
        apply eq_of_heq, apply heq.subst Happ,
        congr' 1; simp [hΓ', Hfn']
       end)
  | Done fn_val :=
    match mk_progress' Γ₂ arg hΓ.right with
    | Step arg' arg_step := Step
      (App Γ fn arg')
      $ EvalLift Γ
        ⟨_, EAppRight Γ₁ (by rw [context.add_zero]) fn_val _ $ EHole γ A⟩
        (App Γ fn arg) (App Γ fn arg')
        (begin rw [context.add_comm] at hΓ', exact hΓ' end)
        arg_step
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Harg: arg == x,
          h_generalize Happ: (App (Γ₂ + Γ₁) fn x) == y,
          apply eq_of_heq, apply heq.subst Happ,
          congr' 1; simp [hΓ', Harg]
        end)
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Harg': arg' == x,
          h_generalize Happ: (App (Γ₂ + Γ₁) fn x) == y,
          apply eq_of_heq, apply heq.subst Happ,
          congr' 1; simp [hΓ', Harg']
        end)
    | Done arg_val :=
      match fn, fn_val with
      | (Abs M), fn_val := Step
        (ssubst Γ M arg)
        $ EvalLam Γ
          M arg_val
      | (Var Γ x hId), hV :=
        begin
          simp [hΓ.left] at hId, exfalso,
          apply matrix.identity_neq_zero,
          exact hId.symm,
        end
      end
    | Conc arg_conc := Conc
      $ comms_blocked.wrap Γ
        arg_conc
        ⟨_, EAppRight Γ₁ (by rw [context.add_zero]) fn_val _ $ EHole γ A⟩
        (App Γ fn arg)
        (by solve_context)
        (begin simp [*, eval_ctx_fn.apply],
          h_generalize Hx: arg == x,
          h_generalize Hy: (App (Γ₂+Γ₁) fn x) == y,
          apply eq_of_heq, apply heq.subst Hy,
          congr' 1; simp [hΓ', Hx]
        end)
    end
  | Conc fn_conc := Conc
    $ comms_blocked.wrap Γ fn_conc
      ⟨_, EAppLeft Γ₂ (by rw [context.zero_add]) arg _ $ EHole γ $ A⊸B⟩
      (App Γ fn arg)
      (by solve_context)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: fn == x,
        h_generalize Hy: (App (Γ₁+Γ₂) x arg) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ', Hx]
      end)
end
| .(γ) _ .(Γ) (@LetUnit γ Γ₁ Γ₂ A Γ M N hΓ) hZero :=
  have hZero: Γ₁ = 0, from begin
    simp at hΓ hZero ⊢, rw [hΓ] at hZero,
    exact context.zeros_left hZero,
  end,
  have h2: Γ = Γ₂ := by simp [hΓ, hZero],
  match mk_progress' Γ₁ M hZero with
  | Step M' M_step := Step
    (LetUnit Γ M' N hΓ)
    $ EvalLift Γ
      ⟨_, ELetUnit Γ₂ (by rw [context.zero_add]) N _ $ EHole γ tp.unit⟩
      (LetUnit Γ M N hΓ) (LetUnit Γ M' N hΓ)
      hΓ M_step
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (LetUnit (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hfn': M' == x,
        h_generalize Happ: (LetUnit (Γ₁ + Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Happ,
        congr' 1; simp [hΓ, Hfn']
       end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ M_conc
      ⟨_, ELetUnit Γ₂ (by rw [context.zero_add]) N _ $ EHole γ tp.unit⟩
      (LetUnit Γ M N hΓ)
      hΓ
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (LetUnit (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Done M_val :=
    match M, M_val with
    | (Unit _ _), M_val := Step (cast (by rw [h2]) N)
      $ (begin
        convert EvalUnit N,
        h_generalize Hx: N == x, exact Hx.symm,
      end)
    | (Var Γ x hId), hV :=
      begin
        simp [hZero] at hId, exfalso,
        apply matrix.identity_neq_zero,
        exact hId.symm,
      end
    end
  end
| .(γ) _ .(Γ) (@LetPair γ Γ₁ Γ₂ A B C Γ M N hΓ) hZero :=
  have hZero: Γ₁ = 0 ∧ Γ₂ = 0, from begin
    simp at hΓ hZero ⊢, rw [hΓ] at hZero,
    exact ⟨context.zeros_left hZero, context.zeros_right hZero⟩,
  end,
  match mk_progress' Γ₁ M hZero.left with
  | Step M' M_step := Step
    (LetPair Γ M' N)
    $ EvalLift Γ
      ⟨_, ELetPair Γ₂ (by rw [context.zero_add]) N _ $ EHole γ _⟩
      (LetPair Γ M N) (LetPair Γ M' N) (by simp [hΓ]) M_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (LetPair (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (LetPair (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ M_conc
      ⟨_, ELetPair Γ₂ (by rw [context.zero_add]) N _ $ EHole γ _⟩
      (LetPair Γ M N) (by simp [hΓ])
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (LetPair (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Done M_val :=
    begin
      clear _match,
      cases M_val,
      case VVar : _ hId {
        exfalso, simp [hZero.left] at hId,
        apply matrix.identity_neq_zero,
        exact hId.symm,
      },
      case VPair : _ _ V W hΓ' V_val W_val {
        apply Step (dsubst Γ N V W $ by simp [hΓ, hΓ']),
        exact EvalPair Γ₁ Γ V_val W_val N (by simp [hΓ, hΓ']),
      },
    end
  end

| .(γ) _ .(Γ) (@Case γ Γ₁ Γ₂ A B C Γ L M N hΓ) hZero :=
  have hZero: Γ₁ = 0 ∧ Γ₂ = 0, from begin
    simp at hΓ hZero ⊢, rw [hΓ] at hZero,
    exact ⟨context.zeros_left hZero, context.zeros_right hZero⟩,
  end,
  match mk_progress' Γ₁ L hZero.left with
  | Step L' L_step := Step
    (Case Γ L' M N)
    $ EvalLift Γ
      ⟨_, ECase Γ₂ (by rw [context.zero_add]) M N _ $ EHole γ $ tp.sum A B⟩
      (Case Γ L M N) (Case Γ L' M N) (by simp [hΓ]) L_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: L == x,
        h_generalize Hy: (Case (Γ₁+Γ₂) x M N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: L' == x,
        h_generalize Hy: (Case (Γ₁+Γ₂) x M N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Conc L_conc := Conc
    $ comms_blocked.wrap Γ L_conc
      ⟨_, ECase Γ₂ (by rw [context.zero_add]) M N _ $ EHole γ $ tp.sum A B⟩
      (Case Γ L M N) (by simp [hΓ])
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hx: L == x,
        h_generalize Hy: (Case (Γ₁+Γ₂) x M N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ, Hx]
      end)
  | Done L_val :=
    match L, L_val with
    | (Inl B V), (VInl _ V_val) := Step
      (ssubst _ M V)
      $ EvalInl Γ V_val M N
    | (Inr A V), (VInr _ V_val) := Step
      (ssubst _ N V)
      $ EvalInr Γ V_val M N
    | (Var _ _ hId), _ :=
      begin
        simp [hZero.left] at hId, exfalso,
        apply matrix.identity_neq_zero,
        exact hId.symm,
      end
    end
  end

/- Communication constructs. -/
| γ A Γ (Fork M) _ :=
  match mk_progress' Γ M with
  | Done M_val := Conc
    ⟨CCFork M_val, ⟨_, EHole γ _⟩, (by rw [context.add_zero]),
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: (Fork M) == x,
        h_generalize Hy: x == y,
        apply eq_of_heq, apply heq.subst Hy,
        exact Hx,
      end)⟩
  | Step M' M_step := Step
    (Fork M')
    $ EvalLift Γ
      ⟨_, EFork _ $ EHole γ _⟩
      (Fork M) (Fork M')
      (by solve_context)
      M_step
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Fork x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (Fork x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ
      M_conc
      ⟨_, EFork _ $ EHole γ _⟩
      (Fork M)
      (by solve_context)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Fork x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
  end
| .(γ) _ .(Γ) (@Send γ Γ₁ Γ₂ A S Γ M N hΓ') hΓ :=
  have hΓ: Γ₁ = 0 ∧ Γ₂ = 0, from begin
    simp at hΓ hΓ' ⊢, rw [hΓ] at hΓ',
    exact ⟨context.zeros_left hΓ'.symm, context.zeros_right hΓ'.symm⟩
  end,
  match mk_progress' Γ₁ M hΓ.left with
  | Step M' M_step := Step
    (Send Γ M' N)
    $ EvalLift Γ
      ⟨_, ESendLeft Γ₂ (by rw [context.zero_add]) N _ $ EHole γ A⟩
      (Send Γ M N) (Send Γ M' N)
      hΓ' M_step
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hfn: M == x,
        h_generalize Happ: (Send (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Happ,
        congr' 1; simp [hΓ', Hfn]
      end)
      (begin
        simp [eval_ctx_fn.apply],
        h_generalize Hfn': M' == x,
        h_generalize Happ: (Send (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Happ,
        congr' 1; simp [hΓ', Hfn']
       end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ
      M_conc
      ⟨_, ESendLeft Γ₂ (by rw [context.zero_add]) N _ $ EHole γ A⟩
      (Send Γ M N)
      (by solve_context)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Send (Γ₁+Γ₂) x N) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [hΓ', Hx]
      end)
  | Done M_val :=
    match mk_progress' Γ₂ N hΓ.right with
    | Step N' N_step := Step
      (Send Γ M N')
      $ EvalLift Γ
        ⟨_, ESendRight Γ₁ (by rw [context.add_zero]) M_val _ $ EHole γ $ !A⬝S⟩
        (Send Γ M N) (Send Γ M N')
        (begin rw [context.add_comm] at hΓ', exact hΓ' end)
        N_step
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Hfn: N == x,
          h_generalize Happ: (Send (Γ₂+Γ₁) M x) == y,
          apply eq_of_heq, apply heq.subst Happ,
          congr' 1; simp [hΓ', Hfn]
        end)
        (begin
          simp [eval_ctx_fn.apply],
          h_generalize Hfn': N' == x,
          h_generalize Happ: (Send (Γ₂+Γ₁) M x) == y,
          apply eq_of_heq, apply heq.subst Happ,
          congr' 1; simp [hΓ', Hfn']
        end)
    | Conc N_conc := Conc
      $ comms_blocked.wrap Γ
        N_conc
        ⟨_, ESendRight Γ₁ (by rw [context.add_zero]) M_val _ $ EHole γ $ !A⬝S⟩
        (Send Γ M N)
        (by solve_context)
        (begin
          simp [*, eval_ctx_fn.apply],
          h_generalize Hx: N == x,
          h_generalize Hy: (Send (Γ₂+Γ₁) M x) == y,
          apply eq_of_heq, apply heq.subst Hy,
          congr' 1; simp [hΓ', Hx]
        end)
    | Done N_val := Conc
      ⟨CCSend Γ M_val N_val, ⟨_, EHole γ _⟩, (by rw [context.add_zero]),
        (begin
          simp [*, eval_ctx_fn.apply],
          h_generalize Hx: (Send Γ M N) == x,
          h_generalize Hy: x == y,
          apply eq_of_heq, apply heq.subst Hy,
          exact Hx,
        end)⟩
    end
  end
| γ A Γ (Recv M) _ :=
  match mk_progress' Γ M with
  | Done M_val := Conc
    ⟨CCRecv M_val, ⟨_, EHole γ _⟩, (by rw [context.add_zero]),
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: (Recv M) == x,
        h_generalize Hy: x == y,
        apply eq_of_heq, apply heq.subst Hy,
        exact Hx,
      end)⟩
  | Step M' M_step := Step
    (Recv M')
    $ EvalLift Γ
      ⟨_, ERecv _ $ EHole γ _⟩
      (Recv M) (Recv M')
      (by solve_context)
      M_step
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Recv x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (Recv x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ
      M_conc
      ⟨_, ERecv _ $ EHole γ _⟩
      (Recv M)
      (by solve_context)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Recv x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
  end
| γ A Γ (Wait M) _ :=
  match mk_progress' Γ M with
  | Done M_val := Conc
    ⟨CCWait M_val, ⟨_, EHole γ _⟩, (by rw [context.add_zero]),
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: (Wait M) == x,
        h_generalize Hy: x == y,
        apply eq_of_heq, apply heq.subst Hy,
        exact Hx,
      end)⟩
  | Step M' M_step := Step
    (Wait M')
    $ EvalLift Γ
      ⟨_, EWait _ $ EHole γ _⟩
      (Wait M) (Wait M')
      (by solve_context)
      M_step
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Wait x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M' == x,
        h_generalize Hy: (Wait x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
  | Conc M_conc := Conc
    $ comms_blocked.wrap Γ
      M_conc
      ⟨_, EWait _ $ EHole γ _⟩
      (Wait M)
      (by solve_context)
      (begin
        simp [*, eval_ctx_fn.apply],
        h_generalize Hx: M == x,
        h_generalize Hy: (Wait x) == y,
        apply eq_of_heq, apply heq.subst Hy,
        congr' 1; simp [Hx]
      end)
  end

def mk_progress {γ} {A: tp} (M: term (0: context γ) A)
  : progress M := mk_progress' 0 M rfl

end progress
