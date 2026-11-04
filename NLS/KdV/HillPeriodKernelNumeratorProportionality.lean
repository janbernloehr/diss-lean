import NLS.KdV.HillEntireRootVariationDecay
import NLS.KdV.HillIntrinsicNumeratorVariationPeriod
import NLS.KdV.HillComplexEntirePeriodInterpolation

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

theorem hillAbelianNumeratorRootVariation_proportional_of_off_period_kernel
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n) (h : Coeff 2)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hkernel : ∀ k : ℕ, 1 ≤ k → k ≠ n →
      fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) (hillGapRootHilbertCoordinates q hq hr roots hroots) h = 0) :
    hillAbelianNumeratorRootVariation n (hillGapRootHilbertCoordinates q hq hr roots hroots) h =
      (fun E => (fderiv ℂ (hillAbelianHilbertPeriod q hq hr n n)
        (hillGapRootHilbertCoordinates q hq hr roots hroots) h/
          hillAbelianCandidatePeriod q hq hr roots n n)*
            hillAbelianHilbertPsi n (E,hillGapRootHilbertCoordinates q hq hr roots hroots)) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let c : ℂ := fderiv ℂ (hillAbelianHilbertPeriod q hq hr n n) a h/hillAbelianCandidatePeriod q hq hr roots n n
  let V := hillAbelianNumeratorRootVariation n a h
  let P : ℂ → ℂ := fun E => hillAbelianHilbertPsi n (E,a)
  let N : ℂ → ℂ := fun E => V E+(-c)*P E
  have hV : AnalyticOnNhd ℂ V univ := analyticOnNhd_hillAbelianNumeratorRootVariation n a h
  have hP : AnalyticOnNhd ℂ P univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  have hM : AnalyticOnNhd ℂ (fun E => (-c)*P E) univ := analyticOnNhd_const.mul hP
  have hN : AnalyticOnNhd ℂ N univ := hV.add hM
  have hIP (k : ℕ) : hillIntrinsicGapPeriod q hq hr k P = hillAbelianHilbertPeriod q hq hr n k a := rfl
  have hp (k : ℕ) (hk : 1 ≤ k) : hillIntrinsicGapPeriod q hq hr k N = 0 := by
    dsimp only [N]
    rw [hillIntrinsicGapPeriod_add q hq hr k hk _ _ hV hM,
      hillIntrinsicGapPeriod_const_mul q hq hr k P (-c),hIP k,
      ← fderiv_hillAbelianHilbertPeriod_eq_intrinsic_variation q hq hr n k hk a h,
      hillAbelianHilbertPeriod_eq_genuine_period q hq hr roots hroots n k]
    by_cases hkn : k = n
    · subst k
      dsimp only [c]
      have hown := hillAbelianCandidatePeriod_own_ne_zero q hq hr roots hroots n hn
      field_simp
      ring
    · rw [hkernel k hk hkn,hperiods k hk hkn,mul_zero,add_zero]
  have hzero : N = 0 := by
    apply complex_entire_eq_zero_of_hill_periods_and_product_decay q hq hr N hN hp
    intro test htest ε hε
    let δ : ℝ := ε/(‖c‖+2)
    have hδ : 0 < δ := by dsimp only [δ];positivity
    filter_upwards [eventually_hillAbelianNumeratorRootVariation_div_full_product_le q hq hr h0q h0r n hn a h test htest δ hδ,
      eventually_hillAbelianHilbertPsi_div_full_product_le q hq hr h0q h0r n hn a test htest δ hδ] with k hkV hkP
    intro E hE
    have hb : ‖N E/hillAbelianNumeratorProduct test 0 E‖ ≤ (1+‖c‖)*δ := by
      dsimp only [N]
      rw [add_div,mul_div_assoc]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_neg]
      have hfirst : ‖V E/hillAbelianNumeratorProduct test 0 E‖ ≤ δ := hkV E hE
      have hsecond : ‖P E/hillAbelianNumeratorProduct test 0 E‖ ≤ δ := hkP E hE
      nlinarith [mul_le_mul_of_nonneg_left hsecond (norm_nonneg c)]
    apply hb.trans
    have he : (‖c‖+2)*δ = ε := by dsimp only [δ];exact mul_div_cancel₀ ε (by positivity : ‖c‖+2 ≠ 0)
    nlinarith
  funext E
  have he := congrFun hzero E
  change V E+(-c)*P E = 0 at he
  change V E = c*P E
  linear_combination he

end NLS.KdV
