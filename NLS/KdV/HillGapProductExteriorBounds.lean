import NLS.KdV.HillGapRootEnergyProduct
import NLS.ZakharovShabat.SingleSpectralProductRatioExterior

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillGapFullEnergyProduct_ratio_bound
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q hq hr) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      hillAbelianNumeratorProduct other 0 E ≠ 0 ∧
      ‖hillAbelianNumeratorProduct roots 0 E/hillAbelianNumeratorProduct other 0 E‖ ≤ 4 := by
  obtain ⟨R,hR⟩ := exists_threshold_entireSingleSpectralProduct_ratio_le_four
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillGapSignedRootFrequency roots) (hillGapSignedRootFrequency other)
    (memℓp_hillGapSignedRootFrequency_displacement q hq hr roots hroots)
    (memℓp_hillGapSignedRootFrequency_displacement q hq hr other hother)
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,?_⟩
  intro k hk E hE
  have hrpos := centralCircleRadius_pos k
  have hnorm : ‖E‖ = (centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have hs : (Complex.sqrt E)^2 = E := by
    have h := Complex.cpow_nat_inv_pow E (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hw : ‖Complex.sqrt E‖ = centralCircleRadius k := by
    have ht := congrArg norm hs
    rw [norm_pow,hnorm] at ht
    nlinarith [norm_nonneg (Complex.sqrt E)]
  have hRk : R ≤ centralCircleRadius k := by
    have h1 : R < (K : ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hK
    have h2 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hsep (m : ℤ) : Real.pi/4 ≤ ‖Complex.sqrt E-(Real.pi : ℂ)*m‖ := by
    have ht := centralCircle_lattice_gap k (show Complex.sqrt E ∈ sphere (0 : ℂ) (centralCircleRadius k) by
      simpa only [mem_sphere,dist_zero_right] using hw) m
    linarith [Real.pi_pos]
  obtain ⟨hden,hbd⟩ := hR (Complex.sqrt E) (by rw [hw]; exact hRk) hsep
  rw [entireSingleSpectralProduct_hillGapFullEnergyProduct q hq hr roots hroots,
    entireSingleSpectralProduct_hillGapFullEnergyProduct q hq hr other hother,hs] at hbd
  rw [entireSingleSpectralProduct_hillGapFullEnergyProduct q hq hr other hother,hs] at hden
  have hc : -2*Complex.sqrt E ≠ 0 := (mul_ne_zero_iff.mp hden).1
  refine ⟨(mul_ne_zero_iff.mp hden).2,?_⟩
  rw [mul_div_mul_left _ _ hc] at hbd
  exact hbd

end NLS.KdV
