import NLS.ZakharovShabat.SourceFiniteGapPointwiseBound
import NLS.ZakharovShabat.SymmetricSignedGapFiniteFibers

/-! # Norm bounds from finitely supported actual signed gaps

On the symmetric real slice the actual periodic gap length is the absolute
signed-gap coordinate. A fixed finite output support and bounded output
norm therefore control the physical source norm by the finite-gap trace bound.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual periodic gap is the absolute signed-gap coordinate on the symmetric slice. -/
theorem periodicGap_symmetricSource_eq_abs_signedGap (a : RealCoeff 2) (n : ℤ) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) n =
      ((|symmetricSourceSignedGapMap (by simp) (by norm_num) a n| : ℝ) : ℂ) := by
  let φ := symmetricRealSourceCoefficients 2 a
  change canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem _) n = _
  apply Complex.ext
  · exact (abs_sourceSignedGapSequence_re_of_reflection_fixed (by simp) (by norm_num) φ
      (symmetricRealSourceCoefficients_reflection_fixed a) n).symm
  · have h := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) n
    simp only [canonicalPeriodicGap,sub_im,h.1,h.2,sub_self,ofReal_im]

/-- Finite signed output support is the same finite support of actual open gaps. -/
theorem symmetricSource_finiteGap_of_signedGap_closed_off_finset
    (a : RealCoeff 2) (S : Finset ℤ)
    (hS : ∀ n ∉ S, symmetricSourceSignedGapMap (by simp) (by norm_num) a n = 0) :
    symmetricRealSourceCoefficients 2 a ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  apply (symmetricSource_finiteGap_iff_finite_signedGap_support (by simp) (by norm_num) a).mpr
  apply S.finite_toSet.subset
  intro n hn
  by_contra hnot
  exact hn (hS n hnot)

/-- A common finite output support bounds the finite gap sum by cardinality times output norm. -/
theorem sourceFiniteGapLengthSum_symmetric_le_card_mul_norm
    (a : RealCoeff 2) (S : Finset ℤ)
    (hS : ∀ n ∉ S, symmetricSourceSignedGapMap (by simp) (by norm_num) a n = 0)
    (hf : symmetricRealSourceCoefficients 2 a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFiniteGapLengthSum (symmetricRealSourceCoefficients 2 a) hf ≤
      (S.card : ℝ) * ‖symmetricSourceSignedGapMap (by simp) (by norm_num) a‖ := by
  have hs : hf.toFinset ⊆ S := by
    intro n hn
    have hgap : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) n ≠ 0 :=
      (Set.Finite.mem_toFinset hf).mp hn
    by_contra hnot
    apply hgap
    rw [periodicGap_symmetricSource_eq_abs_signedGap,hS n hnot]
    simp
  have hnorm (n : ℤ) : ‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) n‖ ≤
      ‖symmetricSourceSignedGapMap (by simp) (by norm_num) a‖ := by
    rw [periodicGap_symmetricSource_eq_abs_signedGap,Complex.norm_real,Real.norm_eq_abs,abs_abs]
    exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (symmetricSourceSignedGapMap (by simp) (by norm_num) a) n
  unfold sourceFiniteGapLengthSum
  calc
    _ ≤ ∑ n ∈ S, ‖canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) n‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ _n ∈ S, ‖symmetricSourceSignedGapMap (by simp) (by norm_num) a‖ :=
      Finset.sum_le_sum fun n _ => hnorm n
    _ = _ := by simp

/-- Bounded signed-gap outputs on a fixed finite support bound the actual source norm. -/
theorem norm_symmetricSource_le_of_finite_signedGap_bound
    (a : RealCoeff 2) (S : Finset ℤ) (R : ℝ)
    (hS : ∀ n ∉ S, symmetricSourceSignedGapMap (by simp) (by norm_num) a n = 0)
    (hbound : ‖symmetricSourceSignedGapMap (by simp) (by norm_num) a‖ ≤ R) :
    ‖symmetricSourceCoefficients 2 a‖ ≤ 2*(S.card : ℝ)*R := by
  have hf := symmetricSource_finiteGap_of_signedGap_closed_off_finset a S hS
  have hg := sourceFiniteGapLengthSum_symmetric_le_card_mul_norm a S hS hf
  have hb := norm_sq_sourceFiniteGap_le_gap_sum (symmetricRealSourceCoefficients 2 a) hf
  have hnonneg : 0 ≤ sourceFiniteGapLengthSum (symmetricRealSourceCoefficients 2 a) hf := by
    unfold sourceFiniteGapLengthSum
    positivity
  have hm := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  change ‖symmetricSourceCoefficients 2 a‖^2 ≤ _ at hb
  nlinarith [norm_nonneg (symmetricSourceCoefficients 2 a)]

end NLS.ZakharovShabat
