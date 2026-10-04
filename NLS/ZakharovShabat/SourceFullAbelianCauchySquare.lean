import NLS.ZakharovShabat.SourceFullAbelianGapBoundary

/-! # Analytic Cauchy squares across complex gaps

The normalized primitive is the selected root times its Cauchy quotient.
Squaring replaces the root by its endpoint polynomial and removes the cut.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def square (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (t : ℂ × CoeffPair p) : ℂ :=
  sourceAngularSelectedPolynomial hp hp1 t.2 n t.1 *
    (sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) t)^2

theorem square_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ (fun z => C.square n (z,ψ)) (ball (C.discs.center n) (C.discs.outer n)) := by
  intro z hz
  have hpoly : AnalyticAt ℂ (sourceAngularSelectedPolynomial hp hp1 ψ n) z :=
    ((analyticAt_id.sub analyticAt_const).pow 2).sub analyticAt_const
  exact hpoly.mul ((C.quotient_slice_analytic n ψ hψ z hz).pow 2)

theorem square_eq_fullPrimitive_sq (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (z : ℂ)
    (hz : z ∈ ball (C.discs.center n) (C.discs.outer n) \ sourcePeriodicSegment hp hp1 ψ n) :
    C.square n (z,ψ) = (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^2 := by
  rw [C.fullPrimitive_eq_cauchy n n ψ hψ z hz]
  simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive,mul_pow,square]
  rw [sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz.2,
    sourceAngularSelectedPolynomial_eq_endpoint_factor]

theorem square_endpoint (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    C.square n (a,ψ) = 0 := by
  rw [square,sourceAngularSelectedPolynomial_eq_endpoint_factor]
  rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl <;> simp

/-- The analytic value on the gap is the square of either boundary profile. -/
theorem square_eq_gapBoundary_sq (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (θ : ℝ) (upper : Bool) :
    C.square n (sourceStandardRootMidpoint hp hp1 ψ n+
      sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ),ψ) = (C.gapBoundary n ψ θ upper)^2 := by
  have hpoly : sourceAngularSelectedPolynomial hp hp1 ψ n
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ)) =
      -(sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))^2 := by
    have htrig := Complex.sin_sq_add_cos_sq (θ:ℂ)
    simp only [← Complex.ofReal_sin,← Complex.ofReal_cos] at htrig
    unfold sourceAngularSelectedPolynomial quadraticRootPolynomial sourceStandardRootHalfGap
    linear_combination (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4*htrig
  simp only [square,hpoly,gapBoundary,mul_pow]
  cases upper <;> simp only [Bool.false_eq_true,↓reduceIte,neg_sq,I_sq,one_mul,neg_mul,mul_assoc]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
