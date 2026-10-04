import NLS.SequenceSpaces.NonnegativeActionGluing

/-! # Gluing maps recovering common real-action values

Local real realization turns recovery at real representatives into the
nonnegative compatibility required by the analytic gluing theorem.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Real representatives determine an analytic map on the entire union
of action balls, in any complete Banach target. -/
theorem eqOn_of_real_action_ball_agreement (hp : p ≠ ⊤)
    {α : Type*} (a : α → Coeff q) (r : α → ℝ)
    (ha : ∀ i, a i ∈ nonnegativeLocus q) (hr : ∀ i, 0 < r i)
    (hreal : ∀ i b, b ∈ ball (a i) (r i) → b ∈ nonnegativeLocus q → ∃ j, a j = b)
    (f g : Coeff q → F)
    (hf : AnalyticOnNhd ℂ f (⋃ i, ball (a i) (r i)))
    (hg : AnalyticOnNhd ℂ g (⋃ i, ball (a i) (r i)))
    (he : ∀ i, f (a i) = g (a i)) : EqOn f g (⋃ i, ball (a i) (r i)) := by
  intro c hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  have hsub : ball (a i) (r i) ⊆ ⋃ j, ball (a j) (r j) :=
    fun _ hb => mem_iUnion.mpr ⟨i,hb⟩
  apply eqOn_of_nonnegativeActions_agreement hp f g _ isOpen_ball (convex_ball _ _)
    (a i) (mem_ball_self (hr i)) (ha i) (hf.mono hsub).differentiableOn
    (hg.mono hsub).differentiableOn ?_ hi
  intro b hb hpos
  obtain ⟨j, hj⟩ := hreal i b hb hpos
  simpa only [hj] using he j

/-- Local analytic factors of one real function glue on their common family
of action balls, assuming each nonnegative point has a real representative. -/
theorem exists_analytic_gluing_of_real_action_ball_recovery (hp : p ≠ ⊤)
    {α : Type*} (a : α → Coeff q) (r : α → ℝ) (f : α → F)
    (ha : ∀ i, a i ∈ nonnegativeLocus q) (hr : ∀ i, 0 < r i)
    (hreal : ∀ i b, b ∈ ball (a i) (r i) → b ∈ nonnegativeLocus q → ∃ j, a j = b)
    (hf : ∀ i, ∃ g : Coeff q → F, AnalyticOnNhd ℂ g (ball (a i) (r i)) ∧
      ∀ j, a j ∈ ball (a i) (r i) → g (a j) = f j) :
    ∃ G : Coeff q → F, AnalyticOnNhd ℂ G (⋃ i, ball (a i) (r i)) ∧
      ∀ i, G (a i) = f i := by
  classical
  choose g hg hrec using hf
  have he (i k : α) (b : Coeff q) (hb : b ∈ ball (a i) (r i) ∩ ball (a k) (r k))
      (hpos : b ∈ nonnegativeLocus q) : g i b = g k b := by
    obtain ⟨j, hj⟩ := hreal i b hb.1 hpos
    have hi : a j ∈ ball (a i) (r i) := hj.symm ▸ hb.1
    have hk : a j ∈ ball (a k) (r k) := hj.symm ▸ hb.2
    simpa only [hj] using (hrec i j hi).trans (hrec k j hk).symm
  obtain ⟨G, hG, hlocal, _⟩ := exists_analyticOnNhd_gluing_nonnegativeActions hp a r g ha hg he
  exact ⟨G, hG, fun i => (hlocal i (mem_ball_self (hr i))).trans (hrec i i (mem_ball_self (hr i)))⟩

end NLS.Coeff
