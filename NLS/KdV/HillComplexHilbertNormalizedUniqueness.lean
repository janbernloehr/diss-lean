import NLS.KdV.HillEntireRootVariationDecay
import NLS.KdV.HillComplexEntirePeriodInterpolation
import NLS.KdV.HillGlobalNormalizedDifferentials

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

theorem hillAbelian_complex_scaled_hilbert_numerator_unique
    (a b : Coeff 2) (n : ℕ) (hn : 1 ≤ n) (A B : ℂ)
    (hperiods : ∀ k : ℕ, 1 ≤ k → A*hillAbelianHilbertPeriod q hq hr n k a =
      B*hillAbelianHilbertPeriod q hq hr n k b) :
    (fun E => A*hillAbelianHilbertPsi n (E,a)) = (fun E => B*hillAbelianHilbertPsi n (E,b)) := by
  let P : ℂ → ℂ := fun E => hillAbelianHilbertPsi n (E,a)
  let Q : ℂ → ℂ := fun E => hillAbelianHilbertPsi n (E,b)
  let F : ℂ → ℂ := fun E => A*P E+(-B)*Q E
  have hP : AnalyticOnNhd ℂ P univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  have hQ : AnalyticOnNhd ℂ Q univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,b) (mem_univ _)).comp
      (f := fun E : ℂ => (E,b)) (analyticAt_id.prod analyticAt_const)
  have hleft : AnalyticOnNhd ℂ (fun E => A*P E) univ := analyticOnNhd_const.mul hP
  have hright : AnalyticOnNhd ℂ (fun E => (-B)*Q E) univ := analyticOnNhd_const.mul hQ
  have hF : AnalyticOnNhd ℂ F univ := hleft.add hright
  have hp (k : ℕ) (hk : 1 ≤ k) : hillIntrinsicGapPeriod q hq hr k F = 0 := by
    dsimp only [F]
    rw [hillIntrinsicGapPeriod_add q hq hr k hk _ _ hleft hright,
      hillIntrinsicGapPeriod_const_mul q hq hr k P A,hillIntrinsicGapPeriod_const_mul q hq hr k Q (-B)]
    change A*hillAbelianHilbertPeriod q hq hr n k a+(-B)*hillAbelianHilbertPeriod q hq hr n k b = 0
    rw [hperiods k hk]
    ring
  have hzero : F = 0 := by
    apply complex_entire_eq_zero_of_hill_periods_and_product_decay q hq hr F hF hp
    intro test htest ε hε
    let δ : ℝ := ε/(‖A‖+‖B‖+1)
    have hδ : 0 < δ := by dsimp only [δ];positivity
    filter_upwards [eventually_hillAbelianHilbertPsi_div_full_product_le q hq hr h0q h0r n hn a test htest δ hδ,
      eventually_hillAbelianHilbertPsi_div_full_product_le q hq hr h0q h0r n hn b test htest δ hδ] with k hk1 hk2
    intro E hE
    have ht : ‖F E/hillAbelianNumeratorProduct test 0 E‖ ≤ (‖A‖+‖B‖)*δ := by
      dsimp only [F]
      rw [add_div,mul_div_assoc,mul_div_assoc]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul,norm_neg]
      have hb1 : ‖P E/hillAbelianNumeratorProduct test 0 E‖ ≤ δ := hk1 E hE
      have hb2 : ‖Q E/hillAbelianNumeratorProduct test 0 E‖ ≤ δ := hk2 E hE
      nlinarith [mul_le_mul_of_nonneg_left hb1 (norm_nonneg A),mul_le_mul_of_nonneg_left hb2 (norm_nonneg B)]
    apply ht.trans
    have he : (‖A‖+‖B‖+1)*δ = ε := by
      dsimp only [δ]
      exact mul_div_cancel₀ ε (by positivity : ‖A‖+‖B‖+1 ≠ 0)
    nlinarith
  funext E
  have he := congrFun hzero E
  change A*P E+(-B)*Q E = 0 at he
  change A*P E = B*Q E
  linear_combination he

theorem hillAbelian_complex_normalized_hilbertPsi_eq_selected
    (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2)
    (hown : hillAbelianHilbertPeriod q hq hr n n a ≠ 0)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianHilbertPeriod q hq hr n k a = 0) :
    (fun E => hillAbelianHilbertPsi n (E,a)/hillAbelianHilbertPeriod q hq hr n n a) =
      hillAbelianSelectedGlobalPsi q hq hr n hn := by
  let roots := (hillAbelianSelectedGlobalRoots q hq hr n hn).val
  have hroots : roots ∈ hillGapRootBox q hq hr := (hillAbelianSelectedGlobalRoots q hq hr n hn).property
  let b := hillGapRootHilbertCoordinates q hq hr roots hroots
  have hb (k : ℕ) : hillAbelianHilbertPeriod q hq hr n k b = hillAbelianCandidatePeriod q hq hr roots n k :=
    hillAbelianHilbertPeriod_eq_genuine_period q hq hr roots hroots n k
  have hpb : hillAbelianHilbertPeriod q hq hr n n b ≠ 0 := by
    rw [hb]
    exact (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  have hperiod (k : ℕ) (hk : 1 ≤ k) :
      (hillAbelianHilbertPeriod q hq hr n n a)⁻¹*hillAbelianHilbertPeriod q hq hr n k a =
        (hillAbelianHilbertPeriod q hq hr n n b)⁻¹*hillAbelianHilbertPeriod q hq hr n k b := by
    by_cases hkn : k = n
    · subst k
      rw [inv_mul_cancel₀ hown,inv_mul_cancel₀ hpb]
    · rw [hperiods k hk hkn,mul_zero,hb,hb]
      have he := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
      rw [if_neg hkn,div_eq_zero_iff] at he
      rw [he.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1,mul_zero]
  have he := hillAbelian_complex_scaled_hilbert_numerator_unique q hq hr h0q h0r a b n hn _ _ hperiod
  funext E
  have hh := congrFun he E
  rw [hillAbelianHilbertPsi_eq_genuine_candidate q hq hr roots hroots n E,hb] at hh
  simpa only [div_eq_mul_inv,mul_comm,hillAbelianSelectedGlobalPsi,roots] using hh

end NLS.KdV
