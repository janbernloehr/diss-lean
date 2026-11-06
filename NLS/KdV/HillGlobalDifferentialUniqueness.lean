import NLS.KdV.HillEntirePeriodInterpolation
import NLS.KdV.HillGlobalDifferentialReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelian_scaled_candidate_unique
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (A B : ℂ) (hA : A.im = 0) (hB : B.im = 0)
    (hperiods : ∀ k : ℕ, 1 ≤ k → A*hillAbelianCandidatePeriod q hq hr roots n k =
      B*hillAbelianCandidatePeriod q hq hr other n k) :
    (fun E => A*hillAbelianPsiCandidate roots n E) = (fun E => B*hillAbelianPsiCandidate other n E) := by
  let F : ℂ → ℂ := fun E => A*hillAbelianPsiCandidate roots n E+(-B)*hillAbelianPsiCandidate other n E
  have hleft : AnalyticOnNhd ℂ (fun E => A*hillAbelianPsiCandidate roots n E) univ :=
    analyticOnNhd_const.mul (analyticOnNhd_hillAbelianPsiCandidate q hq hr roots hroots n)
  have hright : AnalyticOnNhd ℂ (fun E => (-B)*hillAbelianPsiCandidate other n E) univ :=
    analyticOnNhd_const.mul (analyticOnNhd_hillAbelianPsiCandidate q hq hr other hother n)
  have hF : AnalyticOnNhd ℂ F univ := hleft.add hright
  have hreal (x : ℝ) : (F (x : ℂ)).im = 0 := by
    dsimp only [F]
    simp only [add_im,mul_im,neg_re,neg_im,hA,hB,
      hillAbelianPsiCandidate_im_eq_zero q hq hr roots hroots n x,
      hillAbelianPsiCandidate_im_eq_zero q hq hr other hother n x,mul_zero,zero_mul,add_zero,neg_zero]
  have hp (k : ℕ) (hk : 1 ≤ k) : hillIntrinsicGapPeriod q hq hr k F = 0 := by
    dsimp only [F]
    rw [hillIntrinsicGapPeriod_add q hq hr k hk _ _ hleft hright,
      hillIntrinsicGapPeriod_const_mul q hq hr k _ A,
      hillIntrinsicGapPeriod_const_mul q hq hr k _ (-B)]
    change A*hillAbelianCandidatePeriod q hq hr roots n k+(-B)*hillAbelianCandidatePeriod q hq hr other n k = 0
    rw [hperiods k hk]
    ring
  have hzero : F = 0 := by
    apply entire_eq_zero_of_hill_periods_and_product_decay q hq hr F hF hreal hp
    intro test htest ε hε
    let δ : ℝ := ε/(‖A‖+‖B‖+1)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    filter_upwards [eventually_hillAbelianPsiCandidate_div_full_product_le q hq hr roots test hroots htest n hn δ hδ,
      eventually_hillAbelianPsiCandidate_div_full_product_le q hq hr other test hother htest n hn δ hδ] with k hk1 hk2
    intro E hE
    have ht : ‖F E/hillAbelianNumeratorProduct test 0 E‖ ≤ (‖A‖+‖B‖)*δ := by
      dsimp only [F]
      rw [add_div,mul_div_assoc,mul_div_assoc]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul,norm_neg]
      nlinarith [mul_le_mul_of_nonneg_left (hk1 E hE) (norm_nonneg A),
        mul_le_mul_of_nonneg_left (hk2 E hE) (norm_nonneg B)]
    apply ht.trans
    have he : (‖A‖+‖B‖+1)*δ = ε := by
      dsimp only [δ]
      exact mul_div_cancel₀ ε (by positivity : ‖A‖+‖B‖+1 ≠ 0)
    nlinarith
  funext E
  have he := congrFun hzero E
  change A*hillAbelianPsiCandidate roots n E+(-B)*hillAbelianPsiCandidate other n E = 0 at he
  linear_combination he

theorem hillAbelian_normalized_candidate_unique
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (hrootsPeriods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hotherPeriods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr other n k = 0) :
    (fun E => hillAbelianPsiCandidate roots n E/hillAbelianCandidatePeriod q hq hr roots n n) =
      (fun E => hillAbelianPsiCandidate other n E/hillAbelianCandidatePeriod q hq hr other n n) := by
  have hA : (hillAbelianCandidatePeriod q hq hr roots n n)⁻¹.im = 0 := by
    rw [Complex.inv_im,hillAbelianCandidatePeriod_im_eq_zero q hq hr roots hroots n n hn,neg_zero,zero_div]
  have hB : (hillAbelianCandidatePeriod q hq hr other n n)⁻¹.im = 0 := by
    rw [Complex.inv_im,hillAbelianCandidatePeriod_im_eq_zero q hq hr other hother n n hn,neg_zero,zero_div]
  have hp (k : ℕ) (hk : 1 ≤ k) :
      (hillAbelianCandidatePeriod q hq hr roots n n)⁻¹*hillAbelianCandidatePeriod q hq hr roots n k =
      (hillAbelianCandidatePeriod q hq hr other n n)⁻¹*hillAbelianCandidatePeriod q hq hr other n k := by
    by_cases hkn : k = n
    · subst k
      rw [inv_mul_cancel₀ (hillAbelianCandidatePeriod_own_ne_zero q hq hr roots hroots n hn),
        inv_mul_cancel₀ (hillAbelianCandidatePeriod_own_ne_zero q hq hr other hother n hn)]
    · rw [hrootsPeriods k hk hkn,hotherPeriods k hk hkn,mul_zero,mul_zero]
  have h := hillAbelian_scaled_candidate_unique q hq hr roots other hroots hother n hn _ _ hA hB hp
  simpa only [div_eq_mul_inv,mul_comm] using h

theorem hillAbelian_normalized_candidate_eq_selected
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0) :
    (fun E => hillAbelianPsiCandidate roots n E/hillAbelianCandidatePeriod q hq hr roots n n) =
      hillAbelianSelectedGlobalPsi q hq hr n hn := by
  apply hillAbelian_normalized_candidate_unique q hq hr roots
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val hroots
    (hillAbelianSelectedGlobalRoots q hq hr n hn).property n hn hperiods
  intro k hk hkn
  have h := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
  rw [if_neg hkn,div_eq_zero_iff] at h
  exact h.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1

end NLS.KdV
