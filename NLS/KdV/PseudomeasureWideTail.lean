import NLS.KdV.PseudomeasureWideComparison
import NLS.KdV.PseudomeasureTailInverse
import NLS.FunctionalAnalysis.EquivalentNormNeumann

/-! # The actual wide endpoint tail inverse in both original shifted norms -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.FunctionalAnalysis

/-- One uniform wide cutoff for each original potential norm ball and regularity. -/
theorem exists_wideEndpointHill_cutoff (r : ℝ) (hr1 : r < 1/2) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2 := by
  obtain ⟨N,_,hc⟩ := exists_endpointHill_cutoff r hr1 (13*R)
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro n hn
  convert hc n ((le_max_left N 2).trans hn) using 1
  ring

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)

include hn hz in
/-- The positive-shift conjugate of the actual wide operator has the explicit small norm bound. -/
theorem norm_wideEndpointHillPerturbation_conjugate_le :
    ‖(w.negativeShiftEquiv r hr (n:ℤ) ⊤).toContinuousLinearMap.comp
      ((wideEndpointHillPerturbation w r hr hr1 n hn z hz q).comp
        (w.negativeShiftEquiv r hr (n:ℤ) ⊤).symm.toContinuousLinearMap)‖ ≤
      13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
  let e := w.negativeShiftEquiv r hr (n:ℤ) ⊤
  have hC : 0 ≤ 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr1).le)
      (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro a
  change ‖e (wideEndpointHillPerturbation w r hr hr1 n hn z hz q (e.symm a))‖ ≤
    (13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖a‖
  have h := (negativeShiftedNorm_wideEndpointHillPerturbation_le w r hr hr1 n hn z hz q (e.symm a)).1
  change ‖e (wideEndpointHillPerturbation w r hr hr1 n hn z hz q (e.symm a))‖ ≤
    _*‖e (e.symm a)‖ at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The actual wide tail inverse on the unchanged original endpoint carrier. -/
def wideEndpointHillTailInverse :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] WeightedCoeff (w.negativeSobolev r) ⊤ :=
  equivalentNormNeumannInverse (w.negativeShiftEquiv r hr (n:ℤ) ⊤)
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz q)
    ((norm_wideEndpointHillPerturbation_conjugate_le w r hr hr1 n hn z hz q).trans hs)

/-- This is a left inverse for the actual original wide equation. -/
theorem wideEndpointHillTailInverse_left (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs
      (a-wideEndpointHillPerturbation w r hr hr1 n hn z hz q a) = a :=
  equivalentNormNeumannInverse_left _ _ _ a

/-- This is a right inverse for the actual original wide equation. -/
theorem wideEndpointHillTailInverse_right (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs a -
      wideEndpointHillPerturbation w r hr hr1 n hn z hz q
        (wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs a) = a :=
  equivalentNormNeumannInverse_right _ _ _ a

/-- Every actual wide tail solution is uniquely this inverse applied to its source. -/
theorem wideEndpointHillTailInverse_unique (a b : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hab : a-wideEndpointHillPerturbation w r hr hr1 n hn z hz q a = b) :
    a = wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs b := by
  rw [← hab,wideEndpointHillTailInverse_left]

/-- The very same actual wide inverse has bound two in both opposite endpoint norms. -/
theorem negativeShiftedNorm_wideEndpointHillTailInverse_le
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr (n:ℤ) ⊤ (wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs a) ≤
      2*w.negativeShiftedNorm r hr (n:ℤ) ⊤ a ∧
    w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ (wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs a) ≤
      2*w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ a := by
  have hT (b : WeightedCoeff (w.negativeSobolev r) ⊤) :=
    negativeShiftedNorm_wideEndpointHillPerturbation_le w r hr hr1 n hn z hz q b
  have he := wideEndpointHillTailInverse_right w r hr hr1 n hn z hz q hs a
  constructor
  · apply norm_equiv_solution_le_two (w.negativeShiftEquiv r hr (n:ℤ) ⊤)
      (wideEndpointHillPerturbation w r hr hr1 n hn z hz q) _ _ _ he
    intro b
    exact (hT b).1.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  · apply norm_equiv_solution_le_two (w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤)
      (wideEndpointHillPerturbation w r hr hr1 n hn z hz q) _ _ _ he
    intro b
    exact (hT b).2.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))

end NLS.KdV
