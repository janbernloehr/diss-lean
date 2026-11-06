import NLS.KdV.HillGapProductExteriorBounds
import NLS.KdV.HillGapEnergyProductSimpleZeros

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem tendsto_hillEnergyCircleRadius :
    Tendsto (fun k : ℕ => (centralCircleRadius k)^2) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨K,hK⟩ := exists_nat_gt (max R 1)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hkr : (K : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (1 : ℝ) ≤ k := by linarith [le_max_right R 1]
  have hc : (k : ℝ) ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_gt_three]
  nlinarith [le_max_left R 1]

theorem hillAbelianPsiCandidate_div_full_product
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ) (hE : (roots (n-1) : ℂ) ≠ E) :
    hillAbelianPsiCandidate roots n E/hillAbelianNumeratorProduct other 0 E =
      (2/((n : ℂ)*Real.pi)*(freeHillValue n : ℂ))/((roots (n-1) : ℂ)-E)*
        (hillAbelianNumeratorProduct roots 0 E/hillAbelianNumeratorProduct other 0 E) := by
  have hp := hillGapFullEnergyProduct_factorization q hq hr roots hroots (n-1) E
  rw [hillGapRootEnergyFactor,Nat.sub_add_cancel hn] at hp
  have hfree : (freeHillValue n : ℂ) ≠ 0 := by
    simpa only [Nat.sub_add_cancel hn] using hillGapRootEnergyFactor_denominator_ne_zero (n-1)
  rw [hp,hillAbelianPsiCandidate]
  field_simp [sub_ne_zero.mpr hE,hfree]

theorem eventually_hillAbelianPsiCandidate_div_full_product_le
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianPsiCandidate roots n E/hillAbelianNumeratorProduct other 0 E‖ ≤ ε := by
  obtain ⟨K,hK⟩ := exists_hillGapFullEnergyProduct_ratio_bound q hq hr roots other hroots hother
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
