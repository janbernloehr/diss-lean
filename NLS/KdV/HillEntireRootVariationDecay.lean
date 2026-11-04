import NLS.KdV.HillEnergyCircleFrequencySeparation

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
include h0q h0r

theorem eventually_hill_numerator_div_product_le_of_free_bound
    (N : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖N E‖ ≤ ‖hillAbelianPsiCandidate hillFreeGapRoot n E‖*C)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖N E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  have hδ : 0 < ε/(C+1) := by positivity
  filter_upwards [eventually_hillAbelianPsiCandidate_div_mixed_full_product_le 0 h0q h0r q hq hr
    hillFreeGapRoot roots (hillFreeGapRoot_mem_box h0q h0r) hroots n hn (ε/(C+1)) hδ] with k hk
  intro E hE
  calc
    ‖N E/hillAbelianNumeratorProduct roots 0 E‖ = ‖N E‖/‖hillAbelianNumeratorProduct roots 0 E‖ := norm_div _ _
    _ ≤ (‖hillAbelianPsiCandidate hillFreeGapRoot n E‖*C)/‖hillAbelianNumeratorProduct roots 0 E‖ :=
      div_le_div_of_nonneg_right (hbound k E hE) (norm_nonneg _)
    _ = C*‖hillAbelianPsiCandidate hillFreeGapRoot n E/hillAbelianNumeratorProduct roots 0 E‖ := by rw [norm_div];ring
    _ ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left (hk E hE) hC
    _ ≤ ε := by
      have he : (C+1)*(ε/(C+1)) = ε := mul_div_cancel₀ ε (by positivity : C+1 ≠ 0)
      nlinarith

theorem eventually_hillAbelianHilbertPsi_div_full_product_le
    (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianHilbertPsi n (E,a)/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  apply eventually_hill_numerator_div_product_le_of_free_bound q hq hr h0q h0r
    (fun E => hillAbelianHilbertPsi n (E,a)) n hn (Real.exp (‖a‖*hillExteriorWeightBound)) (by positivity) ?_ roots hroots ε hε
  intro k E hE
  have hsep := hillEnergyCircle_sqrt_free_separation k E hE
  have hz := notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/4) hsep
  have hb := norm_hillAbelianHilbertPsi_exterior_le n (Complex.sqrt E) hz hsep a
  have hs : (Complex.sqrt E)^2 = E := by
    have h := Complex.cpow_nat_inv_pow E (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  simpa only [hs] using hb

theorem eventually_hillAbelianNumeratorRootVariation_div_full_product_le
    (n : ℕ) (hn : 1 ≤ n) (a h : Coeff 2)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianNumeratorRootVariation n a h E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  apply eventually_hill_numerator_div_product_le_of_free_bound q hq hr h0q h0r
    (hillAbelianNumeratorRootVariation n a h) n hn
    (2*Real.exp ((‖a‖+2)*hillExteriorWeightBound)*‖h‖) (by positivity) ?_ roots hroots ε hε
  intro k E hE
  have hsep := hillEnergyCircle_sqrt_free_separation k E hE
  have hz := notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/4) hsep
  have hb := norm_hillAbelianNumeratorRootVariation_exterior_le n (Complex.sqrt E) hz hsep a h
  have hs : (Complex.sqrt E)^2 = E := by
    have ht := Complex.cpow_nat_inv_pow E (Nat.succ_ne_zero 1)
    norm_num at ht
    simpa only [Complex.sqrt,one_div] using ht
  rw [hs] at hb
  apply hb.trans_eq
  ring

end NLS.KdV
