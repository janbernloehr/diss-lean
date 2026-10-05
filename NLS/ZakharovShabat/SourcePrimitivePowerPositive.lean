import NLS.ZakharovShabat.SourcePrimitivePowerRealIntegral
import NLS.ZakharovShabat.SourceRealGapArcoshBound

/-! # Positivity and zero detection for primitive-power moments

Every real-source moment is real and nonnegative. Every odd moment is
strictly positive precisely when its selected periodic gap is open.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem realGapAffinePoint_cos_mem_Icc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) :
    realGapAffinePoint hp hp1 φ.val n (Real.cos θ) ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
  have hz := sourceCanonicalRootGapPoint_mem_segment hp hp1 φ.val n (Real.cos θ)
    (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
  have h := sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val n _ hz
  rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n,ofReal_re] at h
  exact h

theorem sourceRealGapCosineProfile_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    Continuous (sourceRealGapCosineProfile hp hp1 φ.val n) := by
  have hc : Continuous (fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)) := by
    unfold realGapAffinePoint
    fun_prop
  exact continuousOn_univ.mp ((sourceRealGapArcoshProfile_spec hp hp1 φ.val φ.property n).1.comp
    hc.continuousOn (fun θ _ => realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ))

theorem sourceRealGapCosineProfile_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) :
    0 ≤ sourceRealGapCosineProfile hp hp1 φ.val n θ :=
  (sourceRealGapArcoshProfile_le_sqrt hp hp1 φ.val φ.property n _
    (realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ)).1

theorem sourceRealGapCosineProfile_pos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) :
    0 < sourceRealGapCosineProfile hp hp1 φ.val n θ := by
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  exact (sourceRealGapArcoshProfile_spec hp hp1 φ.val φ.property n).2.2.2 _
    (realGapAffinePoint_mem_Ioo hp hp1 φ.val n hopen (cos_mem_gapInterior hθ))

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- Every odd moment has zero imaginary part on the real source locus. -/
theorem real_odd_moment_im (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    (A.moment n (2*m+1) φ.val).im = 0 := by
  rw [A.real_odd_moment_eq_cosineIntegral φ n m]
  rfl

/-- The odd moments detect every open real gap, not just the first moment. -/
theorem real_odd_moment_pos (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    0 < (A.moment n (2*m+1) φ.val).re := by
  rw [A.real_odd_moment_eq_cosineIntegral φ n m,ofReal_re]
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hwidth : 0 < (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
    simpa only [canonicalPeriodicGap,sub_re,sub_pos] using hopen
  apply mul_pos (div_pos hwidth Real.pi_pos)
  apply intervalIntegral.integral_pos Real.pi_pos
    (Real.continuous_sin.mul ((sourceRealGapCosineProfile_continuous hp hp1 φ n).pow (2*m+1))).continuousOn
  · intro θ hθ
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
      (pow_nonneg (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ) _)
  · refine ⟨Real.pi/2,⟨by positivity,by linarith [Real.pi_pos]⟩,?_⟩
    apply mul_pos (by rw [Real.sin_pi_div_two]; exact zero_lt_one)
    exact pow_pos (sourceRealGapCosineProfile_pos hp hp1 φ n hgap _
      ⟨by positivity,by linarith [Real.pi_pos]⟩) _

/-- Lemma 21.1(iv): an odd moment vanishes exactly when its gap closes. -/
theorem real_odd_moment_eq_zero_iff (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    A.moment n (2*m+1) φ.val = 0 ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
  constructor
  · intro hzero
    by_contra hgap
    have hpos := A.real_odd_moment_pos φ n m hgap
    rw [hzero,zero_re] at hpos
    exact (lt_irrefl 0) hpos
  · intro hgap
    exact A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hgap (2*m+1)

/-- All natural orders, including zero, give nonnegative real moments. -/
theorem real_moment_nonneg (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    0 ≤ (A.moment n m φ.val).re ∧ (A.moment n m φ.val).im = 0 := by
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' m
  · rw [hk,A.moment_even φ.val (A.realType_subset_domain φ.property) n k]
    exact ⟨le_rfl,rfl⟩
  · rw [hk]
    refine ⟨?_,A.real_odd_moment_im φ n k⟩
    by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
    · rw [(A.real_odd_moment_eq_zero_iff φ n k).mpr hgap]
      exact le_rfl
    · exact (A.real_odd_moment_pos φ n k hgap).le

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
