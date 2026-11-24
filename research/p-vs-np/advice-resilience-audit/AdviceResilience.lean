/-!
Formal verification of two structural properties from the P vs NP adversarial audit:
1. Syntactic non-invariance of the violation-count partition sum Z_φ(z).
2. Information-theoretic pigeonhole bound: k < n advice bits cannot surject onto 2^n solutions.
-/

namespace PnPAdviceAudit

/-- Violation count on a single-variable assignment `b : Bool` for a list of positive unit clauses. -/
def unitClauseViolations (numClauses : Nat) (b : Bool) : Nat :=
  if b then 0 else numClauses

/-- Partition evaluation at integer base `z` for 1-variable repeated unit clauses. -/
def partitionEval1Var (numClauses : Nat) (z : Nat) : Nat :=
  z ^ (unitClauseViolations numClauses true) + z ^ (unitClauseViolations numClauses false)

/-- Logical satisfiability is invariant under duplicating a clause. -/
theorem pnpAdv_logical_equiv_duplicate (b : Bool) :
    (unitClauseViolations 1 b == 0) = (unitClauseViolations 2 b == 0) := by
  cases b <;> rfl

/-- Partition sum Z_φ(z) is NOT invariant under duplicating a clause (witness at z = 2). -/
theorem pnpAdv_syntax_non_invariance :
    partitionEval1Var 1 2 ≠ partitionEval1Var 2 2 := by
  decide

/-- Elementary pigeonhole principle for `Fin`: an injection `Fin m → Fin a` implies `m ≤ a`. -/
theorem pnpAdv_fin_inj_le : ∀ {m a : Nat} (g : Fin m → Fin a), Function.Injective g → m ≤ a
  | 0, _, _, _ => Nat.zero_le _
  | m + 1, 0, g, _ => Fin.elim0 (g ⟨0, Nat.zero_lt_succ m⟩)
  | m + 1, a + 1, g, hinj => by
      let top : Fin (a + 1) := ⟨a, Nat.lt_succ_self a⟩
      -- Either `top` is in the range of `g` or not; restrict `g` to `Fin m → Fin a`.
      have hsub : ∃ h : Fin m → Fin a, Function.Injective h := by
        by_cases hhit : ∃ i : Fin (m + 1), g i = top
        · obtain ⟨i₀, hi₀⟩ := hhit
          let skip : Fin m → Fin (m + 1) := fun j =>
            if j.val < i₀.val then ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩
            else ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
          have hskip_inj : Function.Injective skip := by
            intro j1 j2 hj
            dsimp [skip] at hj
            split at hj <;> split at hj
            · exact Fin.ext (Fin.mk.inj hj)
            · next h1 h2 =>
              have : j1.val = j2.val + 1 := Fin.mk.inj hj
              omega
            · next h1 h2 =>
              have : j1.val + 1 = j2.val := Fin.mk.inj hj
              omega
            · have : j1.val + 1 = j2.val + 1 := Fin.mk.inj hj
              exact Fin.ext (Nat.succ.inj this)
          have hne : ∀ j : Fin m, (g (skip j)).val < a := by
            intro j
            have hne_top : g (skip j) ≠ top := by
              intro heq
              have := hinj (heq.trans hi₀.symm)
              dsimp [skip] at this
              split at this
              · next h1 =>
                have : j.val = i₀.val := Fin.mk.inj this
                omega
              · next h1 =>
                have : j.val + 1 = i₀.val := Fin.mk.inj this
                omega
            have hlt : (g (skip j)).val < a + 1 := (g (skip j)).isLt
            have hneq : (g (skip j)).val ≠ a := fun hval => hne_top (Fin.ext hval)
            omega
          refine ⟨fun j => ⟨(g (skip j)).val, hne j⟩, ?_⟩
          intro j1 j2 hj
          have hg : g (skip j1) = g (skip j2) := Fin.ext (Fin.mk.inj hj)
          exact hskip_inj (hinj hg)
        · have hne : ∀ j : Fin m, (g ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩).val < a := by
            intro j
            let idx : Fin (m + 1) := ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩
            have hneq : g idx ≠ top := fun heq => hhit ⟨idx, heq⟩
            have hval : (g ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩).val ≠ a := fun h => hneq (Fin.ext h)
            have hlt : (g ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩).val < a + 1 := (g idx).isLt
            omega
          refine ⟨fun j => ⟨(g ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩).val, hne j⟩, ?_⟩
          intro j1 j2 hj
          have hg : g ⟨j1.val, Nat.lt_trans j1.isLt (Nat.lt_succ_self m)⟩ =
                    g ⟨j2.val, Nat.lt_trans j2.isLt (Nat.lt_succ_self m)⟩ := Fin.ext (Fin.mk.inj hj)
          exact Fin.ext (Fin.mk.inj (hinj hg))
      obtain ⟨h, h_inj⟩ := hsub
      exact Nat.succ_le_succ (pnpAdv_fin_inj_le h h_inj)

/-- Pigeonhole bound: no function from Fin (2^k) to Fin (2^n) can be surjective when k < n. -/
theorem pnpAdv_advice_pigeonhole_bound (k n : Nat) (hkn : k < n) :
    ¬ ∃ f : Fin (2 ^ k) → Fin (2 ^ n), Function.Surjective f := by
  intro ⟨f, hsurj⟩
  have hpow : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hkn
  let g : Fin (2 ^ n) → Fin (2 ^ k) := fun y => Classical.choose (hsurj y)
  have hg_inj : Function.Injective g := by
    intro y1 y2 hy
    have h1 : f (g y1) = y1 := Classical.choose_spec (hsurj y1)
    have h2 : f (g y2) = y2 := Classical.choose_spec (hsurj y2)
    rw [← h1, ← h2, hy]
  have hle : 2 ^ n ≤ 2 ^ k := pnpAdv_fin_inj_le g hg_inj
  omega

end PnPAdviceAudit
