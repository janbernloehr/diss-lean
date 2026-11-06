import NLS.KdV.HillAbelianCosinePeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianCosinePrimitive_zero (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    hillAbelianCosinePrimitive q hq hr n hn k 0 = -(Real.pi : ℂ)*(if k = n then 1 else 0) := by
  obtain ⟨Ω,hΩ,_,hseg,_,hder⟩ := exists_hillAbelianCosinePrimitive_analytic_chart q hq hr n hn k hk
  let F := hillAbelianCosinePrimitive q hq hr n hn k
  let D := hillAbelianCosineDifferential q hq hr n hn k
  have hangle (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) : (θ : ℂ) ∈ Ω := by
    apply hseg
    exact ofReal_mem_ordered_segment 0 Real.pi θ Real.pi_pos.le hθ
  have hcontF : ContinuousOn (fun θ : ℝ => F (θ : ℂ)) (Icc 0 Real.pi) :=
    (show ContinuousOn F Ω from fun θ hθ => (hder θ hθ).continuousAt.continuousWithinAt).comp
      continuous_ofReal.continuousOn hangle
  have hcontD : ContinuousOn (fun θ : ℝ => D (θ : ℂ)) (Icc 0 Real.pi) := by
    intro θ _
    exact ((analyticAt_hillAbelianCosineDifferential_real q hq hr n hn k hk θ).continuousAt.comp
      continuous_ofReal.continuousAt).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le hcontF
    (fun θ hθ => (hder _ (hangle θ (Ioo_subset_Icc_self hθ))).comp_ofReal)
      (hcontD.intervalIntegrable_of_Icc Real.pi_pos.le)
  dsimp only [F] at hFTC
  rw [integral_hillAbelianCosineDifferential q hq hr n hn k hk,
    hillAbelianCosinePrimitive_pi q hq hr n hn k,ofReal_zero,zero_sub] at hFTC
  change _ = -F 0 at hFTC
  simpa only [neg_mul,F] using neg_eq_iff_eq_neg.mp hFTC.symm

end NLS.KdV
