import NLS.KdV.HillFiniteIntrinsicPeriodMap
import NLS.KdV.HillHighIntrinsicPeriodComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillMixedComplexPeriodSequence (N n : ℕ) (t : Coeff 2 × Coeff 2) : Coeff 2 :=
  hillLowComplexPeriodSequence q hq hr N n t+hillComplexScaledTailPeriodSequence h0q h0r N n t

theorem analyticOnNhd_hillMixedComplexPeriodSequence
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (U : Set (Coeff 2))
    (hperiods : ∀ k : ℕ, 1 ≤ k → k < N →
      AnalyticOnNhd ℂ (hillAbelianComplexPeriod q hq hr n k) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N n) (univ ×ˢ (U ∩ ball 0 B)) := by
  have hlo := analyticOnNhd_hillLowComplexPeriodSequence q hq hr N n U hperiods
  have hhi := analyticOnNhd_hillComplexScaledTailPeriodSequence h0q h0r N n hN hn B D hD hc
  exact (hlo.mono (fun _ ht => ⟨mem_univ _,ht.2.1⟩)).add
    (hhi.mono (fun _ ht => ⟨mem_univ _,ht.2.2⟩))

theorem exists_hillMixedComplexPeriodSequence_analytic_neighborhood :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1 ≤ N ∧ 0 < D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧ U ⊆ ball 0 B ∧
          ∀ n : ℕ, 1 ≤ n →
            AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N n) (univ ×ˢ U) := by
  let B : ℝ := ‖SpectralWeight.one.toCoeff q‖+1
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  obtain ⟨V,hV,hqV,hperiods⟩ := exists_hillAbelianComplexPeriods_common_finite_neighborhood q hq hr N
  refine ⟨N,B,D,V ∩ ball 0 B,hN,hD,hcontrol,hV.inter isOpen_ball,?_,inter_subset_right,?_⟩
  · refine ⟨hqV,?_⟩
    rw [mem_ball,dist_zero_right]
    dsimp only [B]
    linarith
  · intro n hn
    exact analyticOnNhd_hillMixedComplexPeriodSequence q hq hr h0q h0r N n hN hn B D hD.le hcontrol V (hperiods n)

end NLS.KdV
