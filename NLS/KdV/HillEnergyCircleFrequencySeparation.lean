import NLS.KdV.HillMixedGapProductDecay
import NLS.KdV.HillExteriorNumeratorVariationBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillEnergyCircle_sqrt_mem_centralCircle (k : ℕ) (E : ℂ)
    (hE : E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2)) :
    Complex.sqrt E ∈ sphere (0 : ℂ) (centralCircleRadius k) := by
  have hs : (Complex.sqrt E)^2 = E := by
    have h := Complex.cpow_nat_inv_pow E (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hnorm : ‖E‖ = (centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have ht := congrArg norm hs
  rw [norm_pow,hnorm] at ht
  have hr := centralCircleRadius_pos k
  have hw : ‖Complex.sqrt E‖ = centralCircleRadius k := by nlinarith [norm_nonneg (Complex.sqrt E)]
  simpa only [mem_sphere,dist_zero_right] using hw

theorem hillEnergyCircle_sqrt_free_separation (k : ℕ) (E : ℂ)
    (hE : E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2)) :
    ∀ m : ℤ, Real.pi/4 ≤ ‖Complex.sqrt E-(Real.pi : ℂ)*m‖ := by
  intro m
  have ht := centralCircle_lattice_gap k (hillEnergyCircle_sqrt_mem_centralCircle k E hE) m
  linarith [Real.pi_pos]

end NLS.KdV
