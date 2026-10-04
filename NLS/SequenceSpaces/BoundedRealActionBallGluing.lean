import NLS.SequenceSpaces.RealActionBallGluing

/-! # Analytic gluing with bounds on a fixed family of action balls

Each local bound survives gluing on the same ball. The ball family is
chosen independently of the target space, so simultaneous refined bounds
can retain one neighborhood for all target exponents.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Bounded local analytic factors glue with their bounds on each original
ball, using only compatibility at real action representatives. -/
theorem exists_bounded_analytic_gluing_of_real_action_ball_recovery (hp : p ≠ ⊤)
    {α : Type*} (a : α → Coeff q) (r : α → ℝ) (f : α → F)
    (ha : ∀ i, a i ∈ nonnegativeLocus q) (hr : ∀ i, 0 < r i)
    (hreal : ∀ i b, b ∈ ball (a i) (r i) → b ∈ nonnegativeLocus q → ∃ j, a j = b)
    (hf : ∀ i, ∃ g : Coeff q → F, AnalyticOnNhd ℂ g (ball (a i) (r i)) ∧
      (∀ j, a j ∈ ball (a i) (r i) → g (a j) = f j) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ ball (a i) (r i), ‖g b‖ ≤ M) :
    ∃ G : Coeff q → F, AnalyticOnNhd ℂ G (⋃ i, ball (a i) (r i)) ∧
      (∀ i, G (a i) = f i) ∧
      ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ ball (a i) (r i), ‖G b‖ ≤ M := by
  classical
  choose g hg hrec M hM hbound using hf
  have he (i k : α) (b : Coeff q) (hb : b ∈ ball (a i) (r i) ∩ ball (a k) (r k))
      (hpos : b ∈ nonnegativeLocus q) : g i b = g k b := by
    obtain ⟨j, hj⟩ := hreal i b hb.1 hpos
    have hi : a j ∈ ball (a i) (r i) := hj.symm ▸ hb.1
    have hk : a j ∈ ball (a k) (r k) := hj.symm ▸ hb.2
    simpa only [hj] using (hrec i j hi).trans (hrec k j hk).symm
  obtain ⟨G,hG,hlocal,_⟩ := exists_analyticOnNhd_gluing_nonnegativeActions hp a r g ha hg he
  refine ⟨G,hG,fun i => (hlocal i (mem_ball_self (hr i))).trans (hrec i i (mem_ball_self (hr i))),?_⟩
  intro i
  refine ⟨M i,hM i,?_⟩
  intro b hb
  rw [hlocal i hb]
  exact hbound i b hb

end NLS.Coeff
