import NLS.KdV.HillActualZeroTailQuadraticOffset
import NLS.KdV.HillActualZeroFiniteHeadQuadraticOffset

/-! A single complex source ball and a single constant bound ALL
retained actual Hill frequency-root offsets by their squared physical
frequency gaps. Finite low/collapsed rows and the uniform tail are
combined before BOTH positive spectral indices. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_common_actual_zero_uniform_quadratic_frequency_offset (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n m : ℕ+, m ≠ n →
        ‖hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusCanonicalZeroSequence n y) ((m:ℕ):ℤ)-
          sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ≤
            L*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖^2 := by
  obtain ⟨rT,LT,hrT,hLT,hU,K,htail⟩ := P.exists_common_actual_zero_tail_quadratic_frequency_offset q hq hr
  let s : Finset ℕ+ := (Finset.range K).image (fun j => (⟨j+1,by omega⟩ : ℕ+))
  obtain ⟨rH,LH,hrH,hLH,hhead⟩ := P.exists_finite_head_actual_zero_quadratic_frequency_offset q hq hr s
  refine ⟨min rT rH,LT+LH,lt_min hrT hrH,add_nonneg hLT hLH,
    (ball_subset_ball (min_le_left _ _)).trans hU,?_⟩
  intro y hy n m hmn
  by_cases hm : K ≤ (m:ℕ)
  · exact (htail y (ball_subset_ball (min_le_left _ _) hy) n m hm hmn).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hLH) (sq_nonneg _))
  · have hms : m ∈ s := by
      apply Finset.mem_image.mpr
      refine ⟨(m:ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
      apply Subtype.ext
      change (m:ℕ)-1+1 = (m:ℕ)
      have := m.pos
      omega
    exact (hhead y (ball_subset_ball (min_le_right _ _) hy) n m hms hmn).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hLT) (sq_nonneg _))

end NLS.KdV.HillProductEquationPatch
