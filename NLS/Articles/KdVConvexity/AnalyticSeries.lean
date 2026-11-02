import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.LocallyUniformSummation
import Mathlib.Data.PNat.Equiv
import Mathlib.Logic.Equiv.Nat

/-! # Analytic summation on the positive-index Hilbert action space

This is the summation argument needed in Proposition 4.7(ii) of
arXiv:1502.05857v1, p. 30. The contour terms and their spectral quadratic
estimates are explicit inputs, not assumed constructions of KdV data.

The sequence-valued realization is proved analytic first, and the scalar
sum is obtained by a continuous linear map. Pointwise convergence is not
used as a substitute for Banach-space analyticity.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

/-- The paper's complex ell2 actions, indexed by strictly positive integers. -/
abbrev ActionSpace := lp (fun _ : ℕ+ => ℂ) 2

/-- The closed positive action quadrant, including all collapsed actions. -/
def positiveQuadrant : Set ActionSpace :=
  {a | ∀ n, (a n).im = 0 ∧ 0 ≤ (a n).re}

/-- A bijection used only to reuse the integer-indexed sequence library. -/
def actionIndexEquiv : ℤ ≃ ℕ+ :=
  Equiv.intEquivNat.trans Equiv.pnatEquivNat.symm

/-- A quadratic Hilbert majorant proves absolute summability of the actual
positive-index coefficients and their sum-of-norms estimate. -/
theorem summable_norm_of_quadratic_bound (a : ActionSpace) (f : ℕ+ → ℂ) (C : ℝ)
    (hb : ∀ n, ‖f n‖ ≤ C * ‖a n‖ ^ 2) :
    Summable (fun n => ‖f n‖) ∧ (∑' n, ‖f n‖) ≤ C * ‖a‖ ^ 2 := by
  have ha : Summable (fun n => ‖a n‖ ^ 2) := by
    simpa using (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hnorm : (∑' n, ‖a n‖ ^ 2) = ‖a‖ ^ 2 := by
    simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a).symm
  have hs := (ha.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hs, (hs.tsum_le_tsum hb (ha.mul_left C)).trans_eq ?_⟩
  rw [tsum_mul_left, hnorm]

/-- A total ell1 realization. On the analytic domain, the quadratic bounds
proved below exclude the zero fallback and recover every given term. -/
def seriesTerms (R : ℕ+ → ActionSpace → ℂ) (a : ActionSpace) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun k => R (actionIndexEquiv k) a)

/-- Quadratically bounded contour terms are the coordinates of the actual
ell1 realization, with no dropped indices or zero fallback. -/
theorem seriesTerms_apply (R : ℕ+ → ActionSpace → ℂ) (a : ActionSpace) (C : ℝ)
    (hb : ∀ n, ‖R n a‖ ≤ C * ‖a n‖ ^ 2) (k : ℤ) :
    seriesTerms R a k = R (actionIndexEquiv k) a := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  apply memℓp_gen
  have hs := (summable_norm_of_quadratic_bound a (fun n => R n a) C hb).1
  simpa only [Function.comp_def, ENNReal.toReal_one, Real.rpow_one] using
    actionIndexEquiv.summable_iff.mpr hs

/-- The sequence-valued sum has a quadratic norm bound in the source Hilbert norm. -/
theorem norm_seriesTerms_le (R : ℕ+ → ActionSpace → ℂ) (a : ActionSpace) (C : ℝ)
    (hb : ∀ n, ‖R n a‖ ≤ C * ‖a n‖ ^ 2) :
    ‖seriesTerms R a‖ ≤ C * ‖a‖ ^ 2 := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, one_div_one, Real.rpow_one,
    seriesTerms_apply R a C hb]
  rw [actionIndexEquiv.tsum_eq (fun n => ‖R n a‖)]
  exact (summable_norm_of_quadratic_bound a (fun n => R n a) C hb).2

/-- The scalar sum is the continuous linear ell1 sum of the constructed terms. -/
theorem tsum_eq_sumCLM (R : ℕ+ → ActionSpace → ℂ) (a : ActionSpace) (C : ℝ)
    (hb : ∀ n, ‖R n a‖ ≤ C * ‖a n‖ ^ 2) :
    (∑' n, R n a) = lp.tsumCLM ℂ ℤ ℂ (seriesTerms R a) := by
  change _ = ∑' k : ℤ, seriesTerms R a k
  simp only [seriesTerms_apply R a C hb]
  exact (actionIndexEquiv.tsum_eq (fun n => R n a)).symm

/-- Coordinate analyticity and locally uniform quadratic action bounds
construct a Banach-analytic ell1 family on the entire given open domain. -/
theorem analyticOnNhd_seriesTerms
    (R : ℕ+ → ActionSpace → ℂ) (V : Set ActionSpace) (hV : IsOpen V)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) V)
    (hb : ∀ a ∈ V, ∃ T : Set ActionSpace, IsOpen T ∧ a ∈ T ∧ T ⊆ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n, ‖R n b‖ ≤ C * ‖b n‖ ^ 2) :
    AnalyticOnNhd ℂ (seriesTerms R) V := by
  apply (Coeff.analytic_realization_of_local_bounds
    (fun a k => R (actionIndexEquiv k) a) hV (fun k => hR (actionIndexEquiv k)) ?_).2
  intro a ha
  obtain ⟨T, hT, haT, hTV, C, hC, hbound⟩ := hb a ha
  refine ⟨T ∩ ball a 1, hT.inter isOpen_ball,
    ⟨haT, mem_ball_self (by norm_num)⟩, fun b hb => hTV hb.1,
    C * (‖a‖ + 1) ^ 2, ?_⟩
  intro b hb
  refine ⟨seriesTerms R b, fun k => seriesTerms_apply R b C (hbound b hb.1) k, ?_⟩
  have hnorm : ‖b‖ ≤ ‖a‖ + 1 := by
    have hdist : ‖b - a‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hb.2
    exact (norm_le_norm_sub_add b a).trans (by linarith)
  exact (norm_seriesTerms_le R b C (hbound b hb.1)).trans (by gcongr)

/-- The analytic series step in Proposition 4.7(ii), on a complex open domain
that can contain the entire positive quadrant. The spectral construction
and quadratic bounds for the KdV terms remain explicit obligations. -/
theorem analyticOnNhd_tsum_of_local_quadratic_bound
    (R : ℕ+ → ActionSpace → ℂ) (V : Set ActionSpace) (hV : IsOpen V)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) V)
    (hb : ∀ a ∈ V, ∃ T : Set ActionSpace, IsOpen T ∧ a ∈ T ∧ T ⊆ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n, ‖R n b‖ ≤ C * ‖b n‖ ^ 2) :
    AnalyticOnNhd ℂ (fun a => ∑' n, R n a) V := by
  have hs := analyticOnNhd_seriesTerms R V hV hR hb
  intro a ha
  have he (b : ActionSpace) (hbV : b ∈ V) :
      (∑' n, R n b) = lp.tsumCLM ℂ ℤ ℂ (seriesTerms R b) := by
    obtain ⟨T, _, hbT, _, C, _, hbound⟩ := hb b hbV
    exact tsum_eq_sumCLM R b C (hbound b hbT)
  apply ((lp.tsumCLM ℂ ℤ ℂ).analyticAt _ |>.comp (hs a ha)).congr
  filter_upwards [hV.mem_nhds ha] with b hbV
  exact (he b hbV).symm

end NLS.Articles.KdVConvexity
