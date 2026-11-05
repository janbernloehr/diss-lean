import NLS.KdV.HillAllDirichletTerminals
import NLS.KdV.HillNativeRegularTerminal

/-! # Native terminal evaluation for every positive Hill gap

The actual Dirichlet root is selected on a small enough fixed contour to
lie in the radius-k inner disc. Its genuine terminal sheet factor multiplies
the native vector quadratic solution. Joint Banach analyticity survives the
moving evaluation, and the full Hilbert norm has a uniform coarse bound.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- One source ball works for every positive gap and native solution in the
common ball. This is a full norm bound, without a summability assertion. -/
theorem exists_hillNative_all_regular_terminal_analytic_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, η ≤ ε → ∀ k : ℕ+,
      ∀ H : ℂ × Coeff 2 → Coeff 2, ∀ C : ℝ, 0 ≤ C →
      AnalyticOnNhd ℂ H (ball (freeHillEnergy k) (3*(k : ℝ)/4) ×ˢ ball (0 : Coeff 2) η) →
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4),
        ‖H (E,u)‖ ≤ C/(k : ℝ)) →
      AnalyticOnNhd ℂ (hillNativeRegularTerminal h0q h0r H k) (ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η, ‖hillNativeRegularTerminal h0q h0r H k u‖ ≤ C/8 := by
  obtain ⟨ε,hε,_,hdata⟩ := exists_hillDirichlet_all_terminal_data h0q h0r
  refine ⟨ε,hε,?_⟩
  intro η hηsmall k H C hC hH hbound
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) ε := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le hηsmall
  let μ := fun u => hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)
  have hμsmall (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖μ u-freeHillEnergy k‖ < (k : ℝ)/16 := by
    exact ((hdata k).2.2 _ (hsource u hu)).1
  have hμinner (u : Coeff 2) (hu : u ∈ ball 0 η) : μ u ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4) :=
    mem_closedBall_iff_norm.mpr (by linarith [hμsmall u hu,show (0 : ℝ) < k by positivity])
  have hμdisc (u : Coeff 2) (hu : u ∈ ball 0 η) : μ u ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4) :=
    mem_ball_iff_norm.mpr (by linarith [hμsmall u hu,show (0 : ℝ) < k by positivity])
  have htermbound (u : Coeff 2) (hu : u ∈ ball 0 η) :
      ‖hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)‖ ≤ (k : ℝ)/8 := by
    exact ((hdata k).2.2 _ (hsource u hu)).2.2
  refine ⟨?_,?_⟩
  · intro u hu
    have hma := ((hdata k).1 _ (hsource u hu)).comp
      (f := Coeff.periodDouble) (Coeff.periodDouble.toContinuousLinearMap.analyticAt u)
    have hta := ((hdata k).2.1 _ (hsource u hu)).comp
      (f := Coeff.periodDouble) (Coeff.periodDouble.toContinuousLinearMap.analyticAt u)
    have hHa := (hH (μ u,u) ⟨hμdisc u hu,hu⟩).comp
      (f := fun u : Coeff 2 => (μ u,u)) (hma.prod analyticAt_id)
    exact (analyticAt_const.mul hta).smul hHa
  · intro u hu
    rw [hillNativeRegularTerminal,norm_smul,norm_mul,norm_I,one_mul]
    have hh := mul_le_mul (htermbound u hu) (hbound u hu (μ u) (hμinner u hu))
      (norm_nonneg _) (by positivity : 0 ≤ (k : ℝ)/8)
    exact hh.trans_eq (by field_simp)

end NLS.KdV
