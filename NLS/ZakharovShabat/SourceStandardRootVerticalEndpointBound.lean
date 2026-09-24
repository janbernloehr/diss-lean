import NLS.ZakharovShabat.SourceCriticalRootRatioHorizontalLimit
import NLS.ZakharovShabat.SourceStandardRootNorm

/-!
# Standard-root bounds at vertically displaced gap endpoints

The exact norm-square identity for a standard root gives a square-root
lower bound on vertical lines through either endpoint of an open real
gap. This is the local estimate needed for the short connectors of a
shrinking slit contour.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed gap point at parameter 1 is the right periodic endpoint. -/
theorem sourceCanonicalRootGapPoint_one_eq_right
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourceCanonicalRootGapPoint hp hp1 ψ n 1 =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n := by
  unfold sourceCanonicalRootGapPoint sourceStandardRootMidpoint
    sourceStandardRootHalfGap canonicalPeriodicMidpoint canonicalPeriodicGap
  norm_num
  ring

/-- The signed gap point at parameter -1 is the left endpoint. -/
theorem sourceCanonicalRootGapPoint_neg_one_eq_left
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourceCanonicalRootGapPoint hp hp1 ψ n (-1) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n := by
  unfold sourceCanonicalRootGapPoint sourceStandardRootMidpoint
    sourceStandardRootHalfGap canonicalPeriodicMidpoint canonicalPeriodicGap
  norm_num
  ring

/-- At the right endpoint, the standard-root norm is at least the
square root of the real gap length times the vertical displacement. -/
theorem sourceStandardRoot_rightEndpoint_vertical_norm_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (y : ℝ) (hy : y ≠ 0) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    Real.sqrt ((b-a)*|y|) ≤
      ‖sourceStandardRoot hp hp1 ψ n
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n + (y:ℂ)*I)‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let z := r + (y:ℂ)*I
  let R := sourceStandardRoot hp hp1 ψ n z
  have hz : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    have hfull := (sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
      hp hp1 ψ hreal n 1 y hy) n
    simpa only [sourceCanonicalRootGapPoint_one_eq_right] using hfull
  have hsq : ‖R‖^2 = ‖l-z‖*‖r-z‖ :=
    sourceStandardRoot_norm_sq hp hp1 ψ n z hz
  have hshort : ‖r-z‖ = |y| := by
    calc
      ‖r-z‖ = ‖-((y:ℂ)*I)‖ := by
        congr 1
        dsimp [z]
        ring
      _ = |y| := by simp
  have hlong : r.re-l.re ≤ ‖l-z‖ := by
    calc
      r.re-l.re = |l.re-r.re| := by
        rw [abs_of_neg (sub_neg.mpr hopen)]
        ring
      _ = |(l-z).re| := by simp [z]
      _ ≤ ‖l-z‖ := Complex.abs_re_le_norm _
  have hprod : (r.re-l.re)*|y| ≤ ‖R‖^2 := by
    rw [hsq,hshort]
    exact mul_le_mul_of_nonneg_right hlong (abs_nonneg y)
  have hnonneg : 0 ≤ (r.re-l.re)*|y| :=
    mul_nonneg (sub_nonneg.mpr hopen.le) (abs_nonneg y)
  have hsqrt : (Real.sqrt ((r.re-l.re)*|y|))^2 =
      (r.re-l.re)*|y| := Real.sq_sqrt hnonneg
  change Real.sqrt ((r.re-l.re)*|y|) ≤ ‖R‖
  nlinarith [Real.sqrt_nonneg ((r.re-l.re)*|y|), norm_nonneg R]

/-- The same square-root lower bound holds on the vertical line through
the left endpoint. -/
theorem sourceStandardRoot_leftEndpoint_vertical_norm_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (y : ℝ) (hy : y ≠ 0) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    Real.sqrt ((b-a)*|y|) ≤
      ‖sourceStandardRoot hp hp1 ψ n
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n + (y:ℂ)*I)‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let z := l + (y:ℂ)*I
  let R := sourceStandardRoot hp hp1 ψ n z
  have hz : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    have hfull := (sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
      hp hp1 ψ hreal n (-1) y hy) n
    simpa only [sourceCanonicalRootGapPoint_neg_one_eq_left] using hfull
  have hsq : ‖R‖^2 = ‖l-z‖*‖r-z‖ :=
    sourceStandardRoot_norm_sq hp hp1 ψ n z hz
  have hshort : ‖l-z‖ = |y| := by
    calc
      ‖l-z‖ = ‖-((y:ℂ)*I)‖ := by
        congr 1
        dsimp [z]
        ring
      _ = |y| := by simp
  have hlong : r.re-l.re ≤ ‖r-z‖ := by
    calc
      r.re-l.re = |r.re-l.re| := by
        rw [abs_of_pos (sub_pos.mpr hopen)]
      _ = |(r-z).re| := by simp [z]
      _ ≤ ‖r-z‖ := Complex.abs_re_le_norm _
  have hprod : (r.re-l.re)*|y| ≤ ‖R‖^2 := by
    calc
      (r.re-l.re)*|y| = |y| * (r.re-l.re) := by ring
      _ ≤ |y| * ‖r-z‖ := mul_le_mul_of_nonneg_left hlong (abs_nonneg y)
      _ = ‖R‖^2 := by rw [hsq,hshort]
  have hnonneg : 0 ≤ (r.re-l.re)*|y| :=
    mul_nonneg (sub_nonneg.mpr hopen.le) (abs_nonneg y)
  have hsqrt : (Real.sqrt ((r.re-l.re)*|y|))^2 =
      (r.re-l.re)*|y| := Real.sq_sqrt hnonneg
  change Real.sqrt ((r.re-l.re)*|y|) ≤ ‖R‖
  nlinarith [Real.sqrt_nonneg ((r.re-l.re)*|y|), norm_nonneg R]

end NLS.ZakharovShabat
