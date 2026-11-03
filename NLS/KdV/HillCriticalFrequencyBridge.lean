import NLS.KdV.HillGapCriticalPoints
import NLS.ComplexAnalysis.DerivativeSquarePullbackOrder

/-! # The actual frequency derivative is the square pullback of the energy derivative, with exact zero-frequency ramification. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem deriv_canonicalDiscriminant_hillL2CoefficientPotential (q : Coeff 2) (z : ℂ) :
    deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential q)) z =
      2*z*deriv (hillL2Discriminant q) (z^2) := by
  rw [show canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential q) =
    (fun w => hillL2Discriminant q (w^2)) by exact funext (canonicalDiscriminant_hillL2CoefficientPotential q)]
  have h := ((analyticOnNhd_hillL2Discriminant q (z^2) (mem_univ _)).differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_id z).pow 2)).deriv
  convert! h using 1
  simp only [id_eq,Nat.reduceSub,pow_one,mul_one]
  ring

theorem canonicalDiscriminant_hill_critical_iff_of_ne_zero (q : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential q)) z = 0 ↔
      deriv (hillL2Discriminant q) (z^2) = 0 := by
  rw [deriv_canonicalDiscriminant_hillL2CoefficientPotential]
  exact mul_eq_zero_iff_left (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hz)

theorem exists_deriv_hillL2Discriminant_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ z : ℂ, deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z ≠ 0 := by
  by_contra! h
  have he := is_const_of_deriv_eq_zero
    (fun z => (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) z (mem_univ z)).differentiableAt)
    h (hillRealLabels q hq hr 0 : ℂ) (hillRealLabels q hq hr 1 : ℂ)
  rw [hillRealLabels_trace_parity q hq hr 0,hillRealLabels_trace_parity q hq hr 1] at he
  norm_num at he


theorem analyticOrderNatAt_canonicalDiscriminant_hill_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    analyticOrderNatAt (deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)))) 0 =
        1+2*analyticOrderNatAt (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q))) 0 := by
  have han := (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).deriv
  obtain ⟨a,ha⟩ := exists_deriv_hillL2Discriminant_ne_zero q hq hr
  have hfin := analyticOrderAt_ne_top_on_connected isPreconnected_univ han (mem_univ a) ha (mem_univ (0 : ℂ))
  rw [show deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q))) =
      (fun z : ℂ => 2*z*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) (z^2)) by
        exact funext (deriv_canonicalDiscriminant_hillL2CoefficientPotential (SpectralWeight.one.toCoeff q))]
  exact analyticOrderNatAt_linear_mul_comp_sq_zero _ (han 0 (mem_univ _)) hfin


end NLS.KdV
