import NLS.ZakharovShabat.SourceExteriorGapKernel
import NLS.ZakharovShabat.SourceStandardRootRealExteriorSign

/-! # The exact signed exterior kernel denominator

Strict ordering of actual gaps determines both the real root sign and
the exterior displacement sign, including closed gap endpoints.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed root and exterior displacement combine into a negative positive-kernel denominator. -/
theorem sourceStandardRoot_mul_exterior_displacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n m : ℤ) (hmn : m ≠ n) (x t : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)
    (ht : t ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m).re) :
    sourceStandardRoot hp hp1 φ.val n (t:ℂ)*((t:ℂ)-(x:ℂ)) =
      -((Real.sqrt |(t-(canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)*
        (t-(canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)| * |t-x| : ℝ):ℂ) := by
  have hnott : (t:ℂ) ∉ sourcePeriodicSegment hp hp1 φ.val n := by
    intro hs
    have htn := sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val n (t:ℂ) hs
    exact Set.disjoint_left.mp (canonicalPeriodicGaps_disjoint hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) hmn) ht htn
  have him := sourceStandardRoot_im_eq_zero_off_selected_realGap_closedGap hp hp1 φ.val φ.property
    (m := n) (n := m) hmn.symm ht
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential φ.val)
    (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) n
  have hsq := congrArg Complex.re (sourceStandardRoot_sq_of_not_mem_segment hp hp1 φ.val n (t:ℂ) hnott)
  simp only [pow_two,mul_re,sub_re,sub_im,ofReal_re,ofReal_im,hends.1,hends.2,him,
    mul_zero,sub_zero] at hsq
  have hsquare : (sourceStandardRoot hp hp1 φ.val n (t:ℂ)).re^2 =
      (t-(canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)*
        (t-(canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) := by
    nlinarith [hsq]
  rw [← hsquare,abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
  have hcast : sourceStandardRoot hp hp1 φ.val n (t:ℂ) =
      ((sourceStandardRoot hp hp1 φ.val n (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using him)
  rw [hcast,← ofReal_sub,← ofReal_mul,← ofReal_neg]
  simp only [ofReal_re]
  congr 1
  rcases lt_or_gt_of_ne hmn with h | h
  · have hu := sourceStandardRoot_re_pos_after_realGap_closedGap hp hp1 φ.val φ.property (m := n) (n := m) h ht
    have htx : t-x < 0 := by
      have hsep := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) h
      linarith [ht.2,hx.1]
    rw [abs_of_pos hu,abs_of_neg htx]
    ring
  · have hu := sourceStandardRoot_re_neg_before_realGap_closedGap hp hp1 φ.val φ.property (m := n) (n := m) h ht
    have htx : 0 < t-x := by
      have hsep := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) h
      linarith [hx.2,ht.1]
    rw [abs_of_neg hu,abs_of_pos htx]
    ring

end NLS.ZakharovShabat
