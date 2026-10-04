import NLS.ZakharovShabat.SourceFullAbelianSquare
import NLS.ZakharovShabat.SourceFullAbelianGapComparison

/-! # Squared primitive errors on complex gaps

The canonical filled square has the same value on both sides of a gap.
Factoring its error against the selected root polynomial preserves two
powers of the gap length, including at a collapsed gap.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Squaring either boundary root gives the selected polynomial. -/
theorem sourceStandardRootGapBoundary_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ)
    (θ : ℝ) (upper : Bool) :
    (sourceStandardRootGapBoundary hp hp1 ψ j θ upper)^2 =
      sourceAngularSelectedPolynomial hp hp1 ψ j
        (sourceStandardRootMidpoint hp hp1 ψ j +
          sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)) := by
  have htrig := Complex.sin_sq_add_cos_sq (θ:ℂ)
  simp only [← Complex.ofReal_sin,← Complex.ofReal_cos] at htrig
  unfold sourceStandardRootGapBoundary sourceAngularSelectedPolynomial quadraticRootPolynomial
    sourceStandardRootHalfGap
  cases upper <;> simp only [Bool.false_eq_true,↓reduceIte,mul_pow,neg_sq,I_sq]
  all_goals linear_combination -(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2/4*htrig

/-- Both side roots are bounded by half the length of the complex gap. -/
theorem norm_sourceStandardRootGapBoundary_le_halfGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ)
    (θ : ℝ) (upper : Bool) :
    ‖sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖/2 := by
  have hs : ‖(Real.sin θ:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
  have h := mul_le_mul_of_nonneg_left hs (norm_nonneg (sourceStandardRootHalfGap hp hp1 ψ j))
  cases upper <;> simpa only [sourceStandardRootGapBoundary,Bool.false_eq_true,↓reduceIte,
    norm_mul,norm_neg,norm_I,one_mul,mul_one,sourceStandardRootHalfGap,
    sourcePeriodicGapDisplacement_apply,norm_div,norm_ofNat] using h

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- A primitive error `|gamma|*E` gives the filled-square error
`|gamma|^2*E*(E+1)` at every cosine point of either complex gap side. -/
theorem fullSquare_add_polynomial_norm_le
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (j : ℤ) (θ : ℝ) (upper : Bool) (E : ℝ) (hE : 0 ≤ E)
    (herr : ‖C.gapBoundary j ψ θ upper-Complex.I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*E) :
    let z := sourceStandardRootMidpoint hp hp1 ψ j +
      sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)
    ‖sourceFullAbelianSquare hp hp1 W j (z,ψ) + sourceAngularSelectedPolynomial hp hp1 ψ j z‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖^2 * E * (E+1) := by
  let F := C.gapBoundary j ψ θ upper
  let w := sourceStandardRootGapBoundary hp hp1 ψ j θ upper
  let G := ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖
  have hG : 0 ≤ G := norm_nonneg _
  have hw : ‖w‖ ≤ G/2 := norm_sourceStandardRootGapBoundary_le_halfGap hp hp1 ψ j θ upper
  have he : F^2+w^2 = (F-I*w)*(F+I*w) := by
    linear_combination w^2*I_sq
  have hplus : ‖F+I*w‖ ≤ G*(E+1) := by
    calc
      ‖F+I*w‖ = ‖(F-I*w)+2*(I*w)‖ := by congr 1; ring
      _ ≤ ‖F-I*w‖+2*‖w‖ := by
        simpa only [norm_mul,norm_ofNat,norm_I,one_mul] using norm_add_le (F-I*w) (2*(I*w))
      _ ≤ G*E+2*(G/2) := add_le_add herr (by linarith)
      _ = G*(E+1) := by ring
  dsimp only
  rw [C.fullSquare_eq_gapBoundary_sq j ψ hψ θ upper,
    ← sourceStandardRootGapBoundary_sq hp hp1 ψ j θ upper]
  change ‖F^2+w^2‖ ≤ G^2*E*(E+1)
  rw [he,norm_mul]
  calc
    _ ≤ (G*E)*(G*(E+1)) := mul_le_mul herr hplus (norm_nonneg _) (mul_nonneg hG hE)
    _ = _ := by ring

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
