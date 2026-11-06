import NLS.KdV.HillDirichletHamiltonianSources
import NLS.KdV.HillDirichletAnalyticLabels

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The genuine physical norming cotangents evaluate the actual Dirichlet
Hamiltonian sources by the exact diagonal Darboux constant. -/
theorem hillLogNormingGradient_dirichletHamiltonianSource_pairing
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q k hk))
      (hillLogNormingGradientCurve q n hn)=-(if n=k then (1/2 : ℂ) else 0) := by
  obtain ⟨a,ha,ha0,hroot,_⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  have he := hillDirichletLogBranch_dirichletHamiltonianSource_fderiv q n k hn hk a ha ha0 hroot
  rw [hillLogNormingGradient_represents_branch q n hn a ha ha0 hroot,
    ←hillPhysicalDirectionPairing_apply] at he
  exact he

/-- Every endpoint cotangent coefficient is recovered from a single actual
transverse source derivative; no choice of a cotangent factor remains. -/
theorem hillNormingCotangent_coefficient_eq_transverse_derivative
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (G : Coeff 2 → ℂ) (c : ℂ)
    (hD : ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
      (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
        c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk)) :
    c=-2*(fderiv ℂ G (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q k hk)) := by
  have he := hD (hillDirichletHamiltonianSource q k hk) (hillDirichletHamiltonianSource_mem_even q k hk)
  rw [hillLogNormingGradient_dirichletHamiltonianSource_pairing q k k hk hk,if_pos rfl] at he
  linear_combination 2*he

/-- The intrinsic endpoint coefficient is bounded by the actual cotangent
operator norm and the actual transverse Dirichlet source norm. -/
theorem hillNormingCotangent_coefficient_norm_le
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (G : Coeff 2 → ℂ) (c : ℂ)
    (hD : ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
      (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
        c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk)) :
    ‖c‖≤2*‖fderiv ℂ G (SpectralWeight.one.toCoeff q.val)‖*
      ‖SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q k hk)‖ := by
  rw [hillNormingCotangent_coefficient_eq_transverse_derivative q k hk G c hD,norm_mul,
    show ‖(-2 : ℂ)‖=(2 : ℝ) by norm_num]
  exact (mul_le_mul_of_nonneg_left ((fderiv ℂ G (SpectralWeight.one.toCoeff q.val)).le_opNorm _)
    (by norm_num : (0 : ℝ)≤2)).trans_eq (by ring)

end NLS.KdV
