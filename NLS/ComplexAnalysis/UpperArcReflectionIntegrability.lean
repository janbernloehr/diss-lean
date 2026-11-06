import NLS.ComplexAnalysis.UpperReflectionCircleIntegrability

/-! # Circle integrability from continuity along the closed upper arc -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate Interval
namespace NLS.ComplexAnalysis

theorem conj_circleMap_zero (r t : ℝ) :
    conj (circleMap 0 r t)=circleMap 0 r (2*Real.pi-t) := by
  apply Complex.ext <;> simp [circleMap_zero_re,circleMap_zero_im,Real.cos_two_pi_sub,Real.sin_two_pi_sub]

/-- Only continuity along the closed upper arc is needed. Reflection on the
open lower arc permits unrelated values at the two real crossings. -/
theorem circleIntegrable_of_continuous_upper_arc_reflection (f : ℂ → ℂ)
    (r : ℝ) (hr : 0<r)
    (hu : ContinuousOn (fun t : ℝ => f (circleMap 0 r t)) (Icc 0 Real.pi))
    (hrf : ∀ z : ℂ, z.im<0 → f z=conj (f (conj z))) :
    CircleIntegrable f 0 r := by
  have hl : ContinuousOn (fun t : ℝ => conj (f (conj (circleMap 0 r t))))
      (Icc Real.pi (2*Real.pi)) := by
    simp_rw [conj_circleMap_zero]
    apply continuous_star.comp_continuousOn
    apply hu.comp (continuous_const.sub continuous_id).continuousOn
    intro t ht
    change 2*Real.pi-t∈Icc (0:ℝ) Real.pi
    constructor <;> linarith [ht.1,ht.2]
  have hlI : IntervalIntegrable (fun t : ℝ => f (circleMap 0 r t)) volume Real.pi (2*Real.pi) := by
    apply (hl.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])).congr_uIoo
    intro t ht
    have hle : Real.pi≤2*Real.pi := by linarith [Real.pi_pos]
    have ht' : Real.pi<t ∧ t<2*Real.pi := by simpa only [uIoo_of_le hle,mem_Ioo] using ht
    symm
    apply hrf
    rw [circleMap_zero_im]
    have hs := Real.sin_pos_of_pos_of_lt_pi
      (show 0<t-Real.pi by linarith [ht'.1])
      (show t-Real.pi<Real.pi by linarith [ht'.2])
    rw [Real.sin_sub_pi] at hs
    exact mul_neg_of_pos_of_neg hr (by linarith)
  exact (hu.intervalIntegrable_of_Icc (by positivity)).trans hlI
end NLS.ComplexAnalysis
