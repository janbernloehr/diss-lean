import NLS.SequenceSpaces.ConjugateCotangent
import NLS.SequenceSpaces.UniformDualCoefficientLimits
import NLS.FunctionalAnalysis.BoundedSegmentLimits
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal

namespace NLS.Coeff



/-- A common square-summable derivative majorant on every bounded Hilbert
ball makes a differentiable family uniformly continuous under bounded
coefficientwise limits. No strong source convergence is assumed. -/
theorem eventually_norm_differentiable_sub_lt_of_bounded_coefficientwise
    {ι α : Type*} {l : Filter α} (F : ι → Coeff 2 → ℂ) (K : Set ι)
    (hF : ∀ y∈K, Differentiable ℂ (F y))
    (hmajor : ∀ M : ℝ, ∃ b : Coeff 2, ∀ q : Coeff 2, ‖q‖≤M → ∀ y∈K, ∀ n : ℤ,
      ‖conjugateCotangent (by simp : (2 : ℝ≥0∞)≠⊤) (by simp : (2 : ℝ≥0∞)≠⊤)
        (fderiv ℂ (F y) q) n‖≤‖b n‖)
    (a : α → Coeff 2) (b : Coeff 2) (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n)))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in l, ∀ y∈K, ‖F y (a k)-F y b‖<ε := by
  obtain ⟨B,hB⟩ := hb.exists_norm_le
  have hdiff : Bornology.IsBounded (range (fun k => a k-b)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B+‖b‖,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [hB _ ⟨k,rfl⟩])
  have ht' (n : ℤ) : Tendsto (fun k => (a k-b) n) l (𝓝 0) := by
    simpa only [lp.coeFn_sub,Pi.sub_apply,sub_self] using (ht n).sub_const (b n)
  obtain ⟨M,hM⟩ := (NLS.BoundedSegmentLimits.bounded_range_segment a b hb).exists_norm_le
  obtain ⟨c,hc⟩ := hmajor M
  filter_upwards [eventually_small_dualPairing_of_bounded_coefficientwise
    (by simp : (2 : ℝ≥0∞)≠⊤) (fun k => a k-b) hdiff ht' c (ε/2) (by positivity)] with k hk y hy
  have hseg (t : ℝ) : HasDerivAt (NLS.BoundedSegmentLimits.segment b (a k)) (a k-b) t := by
    convert! ((Complex.ofRealCLM.hasDerivAt (x := t)).smul_const (a k-b)).const_add b using 1
    simp
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => F y (NLS.BoundedSegmentLimits.segment b (a k) s))
      ((fderiv ℂ (F y) (NLS.BoundedSegmentLimits.segment b (a k) t)) (a k-b)) t :=
    ((hF y hy _).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hseg t)
  have hbound (t : ℝ) (htm : t∈Icc (0 : ℝ) 1) :
      ‖(fderiv ℂ (F y) (NLS.BoundedSegmentLimits.segment b (a k) t)) (a k-b)‖≤ε/2 := by
    have h := hk (conjugateCotangent (by simp : (2 : ℝ≥0∞)≠⊤) (by simp : (2 : ℝ≥0∞)≠⊤)
      (fderiv ℂ (F y) (NLS.BoundedSegmentLimits.segment b (a k) t)))
      (hc _ (hM _ ⟨(k,⟨t,htm⟩),rfl⟩) y hy)
    rw [dualPairing_conjugateCotangent] at h
    exact h.le
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hbound
    (by simp : (0 : ℝ)∈Icc (0 : ℝ) 1) (by simp : (1 : ℝ)∈Icc (0 : ℝ) 1)
  simp only [NLS.BoundedSegmentLimits.segment_one,NLS.BoundedSegmentLimits.segment_zero,
    sub_zero,norm_one,mul_one] at h
  exact h.trans_lt (by linarith)

end NLS.Coeff
