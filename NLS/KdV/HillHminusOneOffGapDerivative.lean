import NLS.KdV.HillHminusOneOffGapSheets
import NLS.ComplexAnalysis.CoshTraceDerivative

/-! # Actual off-gap Hill discriminant roots and the action differential -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusOffGapRoot_ne_zero
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (z : ℂ) (hz : z ∈ hillHminusGapSquareDisc n r) (hgap : z ∉ segment ℝ l u)
    (htrace : 2*cosh (hillHminusOffGapPrimitive n r K q l u z) =
      (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z) :
    hillHminusOffGapRoot n r K q l u z ≠ 0 := by
  intro he
  have hs := hillHminusOffGapRoot_sq n r K q l u z htrace
  rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hs
  rcases (hpair.zeros_iff z hz).mp hs.symm with heq | heq
  · apply hgap
    rw [heq]
    exact left_mem_segment ℝ l u
  · apply hgap
    rw [heq]
    exact right_mem_segment ℝ l u

theorem hasDerivAt_hillHminusOffGapPrimitive
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (z : ℂ)
    (hz : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) :
    HasDerivAt (hillHminusOffGapPrimitive n r K q l u)
      (deriv (hillHminusDiscriminant q) z/hillHminusOffGapRoot n r K q l u z) z := by
  have ht (w : ℂ) (hw : w ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) :
      2*cosh (hillHminusOffGapPrimitive n r K q l u w) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q w :=
    hillHminusOffGapPrimitive_trace n r hr K q l u hpair w hw.2 (hf w hw.1) (htrace w hw.1)
  have hclosed : IsClosed (segment ℝ l u) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image (AffineMap.lineMap_continuous)).isClosed
  apply hasDerivAt_of_cosh_trace _ _ _
    (isOpen_ball.sdiff hclosed)
    (analyticOnNhd_hillHminusOffGapPrimitive n r K q l u _ hS) ?_
    ((-1 : ℂ)^(n : ℕ)) (by rw [pow_two,← mul_pow]; simp) ht z hz
    (hillHminusOffGapRoot_ne_zero n r K q l u hpair z (ball_subset_closedBall hz.1) hz.2 (ht z hz))
  intro w _
  exact (analyticOnNhd_hillHminusDiscriminant_joint (w,q) (mem_univ _)).comp
    (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)

theorem sinh_add_hill_index (z : ℂ) (n : ℕ) :
    sinh (z+I*(n : ℂ)*Real.pi) = (-1 : ℂ)^n*sinh z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z+I*((n+1 : ℕ) : ℂ)*Real.pi =
        (z+I*(n : ℂ)*Real.pi)+(Real.pi : ℂ)*I := by push_cast; ring
    rw [he,sinh_add_pi_mul_I,ih,pow_succ]
    ring

/-- Matching the shifted primitive identifies the ACTUAL free-normalized
source root, rather than merely another square root of the same radicand. -/
theorem hillHminusOffGapRoot_eq_continued
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u z : ℂ) (ht : (z,q) ∈ hillHminusContinuationDomain)
    (he : hillHminusOffGapPrimitive n r K q l u z =
      hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi) :
    hillHminusOffGapRoot n r K q l u z = hillHminusContinuedRoot (z,q) := by
  rw [hillHminusOffGapRoot,he,sinh_add_hill_index]
  have hs : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
  calc
    _ = 2*sinh (hillHminusContinuedPrimitive (z,q)) := by linear_combination 2*sinh (hillHminusContinuedPrimitive (z,q))*hs
    _ = _ := (hillHminusContinuedPrimitive_trace (z,q) ht).2

end NLS.KdV
