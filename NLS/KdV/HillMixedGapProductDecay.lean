import NLS.KdV.HillGapNumeratorDecay
import NLS.ZakharovShabat.SingleSpectralProductRatioExterior

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillGapFullEnergyProduct_mixed_ratio_bound
    (q' : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq' : SpectralWeight.one.toCoeff q' ∈ Coeff.paritySubspace 0)
    (hr' : IsRealHillPotential (SpectralWeight.one.toCoeff q'))
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q' hq' hr') :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      hillAbelianNumeratorProduct other 0 E ≠ 0 ∧
      ‖hillAbelianNumeratorProduct roots 0 E/hillAbelianNumeratorProduct other 0 E‖ ≤ 4 := by
  obtain ⟨R,hR⟩ := exists_threshold_entireSingleSpectralProduct_ratio_le_four
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillGapSignedRootFrequency roots) (hillGapSignedRootFrequency other)
    (memℓp_hillGapSignedRootFrequency_displacement q hq hr roots hroots)
    (memℓp_hillGapSignedRootFrequency_displacement q' hq' hr' other hother)
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
    entireSingleSpectralProduct_hillGapFullEnergyProduct q' hq' hr' other hother,hs] at hbd
  rw [entireSingleSpectralProduct_hillGapFullEnergyProduct q' hq' hr' other hother,hs] at hden
  have hc : -2*Complex.sqrt E ≠ 0 := (mul_ne_zero_iff.mp hden).1
  refine ⟨(mul_ne_zero_iff.mp hden).2,?_⟩
  rw [mul_div_mul_left _ _ hc] at hbd
  exact hbd

theorem eventually_hillAbelianPsiCandidate_div_mixed_full_product_le
    (q' : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq' : SpectralWeight.one.toCoeff q' ∈ Coeff.paritySubspace 0)
    (hr' : IsRealHillPotential (SpectralWeight.one.toCoeff q'))
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q' hq' hr') (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianPsiCandidate roots n E/hillAbelianNumeratorProduct other 0 E‖ ≤ ε := by
  obtain ⟨K,hK⟩ := exists_hillGapFullEnergyProduct_mixed_ratio_bound q hq hr q' hq' hr' roots other hroots hother
  let C : ℝ := ‖2/((n : ℂ)*Real.pi)*(freeHillValue n : ℂ)‖
  have hC : 0 ≤ C := norm_nonneg _
  filter_upwards [eventually_ge_atTop K,
    tendsto_hillEnergyCircleRadius.eventually_ge_atTop (‖(roots (n-1) : ℂ)‖+4*C/ε+1)] with k hk hbig
  intro E hE
  have hnorm : ‖E‖ = (centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have hdist : 4*C/ε+1 ≤ ‖(roots (n-1) : ℂ)-E‖ := by
    have ht := norm_sub_norm_le E (roots (n-1) : ℂ)
    rw [norm_sub_rev E] at ht
    linarith
  have hdpos : 0 < ‖(roots (n-1) : ℂ)-E‖ := by
    have hh : 0 ≤ 4*C/ε := by positivity
    linarith
  have hne : (roots (n-1) : ℂ) ≠ E := sub_ne_zero.mp (norm_pos_iff.mp hdpos)
  rw [hillAbelianPsiCandidate_div_full_product q hq hr roots other hroots n hn E hne,norm_mul,norm_div]
  have hb := (hK k hk E hE).2
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ C/‖(roots (n-1) : ℂ)-E‖)).trans
  change C/‖(roots (n-1) : ℂ)-E‖*4 ≤ ε
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hdpos).mpr
  have hleft : 4*C/ε ≤ ‖(roots (n-1) : ℂ)-E‖ := by linarith
  have hh := (div_le_iff₀ hε).mp hleft
  nlinarith

end NLS.KdV
