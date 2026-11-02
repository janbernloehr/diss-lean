import NLS.KdV.ClassicalCriticalNumerator
import NLS.KdV.ClassicalSourcePrimitive

/-! # Actual analytic period entries for the moving numerator basis

Use the constructed root continued from the free potential on proved free
isolating contours. Each period entry is analytic on a constructed complex
potential neighborhood and equals the Kronecker delta at zero. These are
the entries of the normalization problem, not an assumed solution of it.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.KdV

theorem classicalHillFreeContour_in_continuationDomain (k : ℕ+) :
    ∀ z ∈ sphere (freeHillEnergy k) (classicalHillFreeFrequencyRadius k),
      (z,(0 : NLS.LinearVolterra.Curve ℂ)) ∈ classicalHillContinuationDomain := by
  obtain ⟨hR, hdisc, hroot, _, _⟩ := Classical.choose_spec (exists_classicalHillFreePsi_periods k)
  intro z hz s _
  have hr : classicalHillRadicand (z,0) ≠ 0 := by
    rw [← classicalHillFreeRoot_sq]
    exact pow_ne_zero 2 (hroot z hz)
  have hgood : (z,(0 : NLS.LinearVolterra.Curve ℂ)) ∈ classicalHillRootDomain :=
    ⟨hdisc (sphere_subset_closedBall hz), hr⟩
  simpa only [ComplexAnalysis.sourceSegmentMap, sub_self, smul_zero, add_zero] using hgood

/-- The actual normalization matrix entry, with the source's `1/(2π)`. -/
def classicalHillCriticalPeriod (n k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ z in C(freeHillEnergy k,classicalHillFreeFrequencyRadius k),
    classicalHillCriticalNumerator n (z,q)/classicalHillContinuedRoot (z,q)

theorem classicalHillCriticalPeriod_free (n k : ℕ+) :
    classicalHillCriticalPeriod n k 0 = if n = k then 1 else 0 := by
  have he := classicalHillFreeFrequencyMoment_zeroth n k
  simp only [classicalHillFreeFrequencyMoment, frequencyMoment, pow_zero, one_mul] at he
  unfold classicalHillCriticalPeriod
  simp only [classicalHillCriticalNumerator_free, classicalHillContinuedRoot_base, he]
  by_cases hnk : n = k
  · rw [if_pos hnk, if_pos hnk, inv_mul_cancel₀]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  · simp only [if_neg hnk, mul_zero]

/-- Every actual entry is analytic near zero, with both the critical
branch and the whole spectral circle valid on that same neighborhood. -/
theorem exists_analytic_classicalHillCriticalPeriod (n k : ℕ+) :
    ∃ V : Set (NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ 0 ∈ V ∧
      V ⊆ classicalHillLocalCriticalDomain n ∧
      (∀ q ∈ V, ∀ z ∈ sphere (freeHillEnergy k) (classicalHillFreeFrequencyRadius k),
        (z,q) ∈ classicalHillContinuationDomain) ∧
      AnalyticOnNhd ℂ (classicalHillCriticalPeriod n k) V := by
  obtain ⟨W, hW, h0W, hcover⟩ := exists_classicalHillContinuation_neighborhood
    (sphere (freeHillEnergy k) (classicalHillFreeFrequencyRadius k)) (isCompact_sphere _ _) 0
    (classicalHillFreeContour_in_continuationDomain k)
  obtain ⟨hV, h0V, _, _, _⟩ := classicalHillLocalCritical_spec n
  let V := W ∩ classicalHillLocalCriticalDomain n
  have hVo : IsOpen V := hW.inter hV
  let D := classicalHillContinuationDomain ∩ (univ ×ˢ classicalHillLocalCriticalDomain n)
  have hD : IsOpen D := isOpen_classicalHillContinuationDomain.inter (isOpen_univ.prod hV)
  have hI : AnalyticOnNhd ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
      classicalHillCriticalNumerator n t/classicalHillContinuedRoot t) D := by
    apply ((analyticOnNhd_classicalHillCriticalNumerator n).mono inter_subset_right).div
      (analyticOnNhd_classicalHillContinuedRoot.mono inter_subset_left)
    intro t ht
    exact classicalHillContinuedRoot_ne_zero t ht.1
  have hcircle : ∀ q ∈ V, ∀ z ∈ sphere (freeHillEnergy k) (classicalHillFreeFrequencyRadius k),
      (z,q) ∈ D := by
    intro q hq z hz
    exact ⟨hcover ⟨hz,hq.1⟩,mem_univ _,hq.2⟩
  refine ⟨V, hVo, ⟨h0W,h0V⟩, inter_subset_right, ?_, ?_⟩
  · intro q hq z hz
    exact (hcircle q hq z hz).1
  have hR := (Classical.choose_spec (exists_classicalHillFreePsi_periods k)).1
  have hi := ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic _ hD hI
    (freeHillEnergy k) (classicalHillFreeFrequencyRadius k) hR.le hVo hcircle
  exact analyticOnNhd_const.mul hi

end NLS.KdV
