import NLS.ZakharovShabat.SourceAbelianCauchyContinuation
import NLS.ComplexAnalysis.NormalizedSegmentPrimitiveUnique

/-! # Choice independence and analytic squares at complex gaps

The exact endpoint normalization identifies different Cauchy charts on
full cut-disc overlaps. Squaring the selected-index primitive removes
the root factor explicitly, giving an analytic function across the
whole complex gap and both endpoints, including collapsed gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianCauchyChart
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {j : ℤ}

/-- Two charts for the same selected gap give exactly the same
 normalized abelian integral on their complete spectral overlap. -/
theorem primitive_eqOn_overlap (D E : SourceAbelianCauchyChart hp hp1 j)
    (ψ : CoeffPair p) (hψD : ψ ∈ D.sources) (hψE : ψ ∈ E.sources) (n : ℤ) :
    EqOn (fun z => D.primitive n (z,ψ)) (fun z => E.primitive n (z,ψ))
      ((ball D.center D.radius ∩ ball E.center E.radius) \ sourcePeriodicSegment hp hp1 ψ j) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j
  have heq := normalized_segment_primitives_eq_on_convex_overlap _
    (fun z => D.primitive n (z,ψ)) (fun z => E.primitive n (z,ψ))
    (ball D.center D.radius) (ball E.center E.radius) l r (I*(Real.pi : ℂ)*(n-j)) (I*(Real.pi : ℂ)*(n-j))
    isOpen_ball isOpen_ball (convex_ball _ _) (convex_ball _ _)
    (D.segment_subset_outer ψ hψD (left_mem_segment ℝ _ _)) (E.segment_subset_outer ψ hψE (left_mem_segment ℝ _ _))
    (D.primitive_derivative n ψ hψD) (E.primitive_derivative n ψ hψE)
    (D.primitive_endpoint_limit n ψ hψD l (by simp [l])) (E.primitive_endpoint_limit n ψ hψE l (by simp [l]))
  intro z hz
  have h := heq hz
  dsimp only at h
  linear_combination h

def square (D : SourceAbelianCauchyChart hp hp1 j) (t : ℂ × CoeffPair p) : ℂ :=
  sourceAngularSelectedPolynomial hp hp1 t.2 j t.1 * (sourceAbelianCauchyQuotient hp hp1 j D.center D.radius t)^2

/-- The selected-index square is analytic on the entire disc for every
 complex source in the chart, including the full segment and its endpoints. -/
theorem square_analytic (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) :
    AnalyticOnNhd ℂ (fun z => D.square (z,ψ)) (ball D.center D.radius) := by
  intro z hz
  have hpoly : AnalyticAt ℂ (sourceAngularSelectedPolynomial hp hp1 ψ j) z :=
    ((analyticAt_id.sub analyticAt_const).pow 2).sub analyticAt_const
  exact hpoly.mul ((D.quotient_slice_analytic ψ hψ z hz).pow 2)

/-- Off the cut the analytic extension is the square of the same
 exactly normalized primitive that agrees with the actual collar values. -/
theorem square_eq_primitive_sq (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p)
    (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 ψ j) :
    D.square (z,ψ) = (D.primitive j (z,ψ))^2 := by
  simp only [primitive,sub_add_cancel,sourceAbelianCauchyPrimitive,mul_pow,square]
  rw [sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ j z hz,sourceAngularSelectedPolynomial_eq_endpoint_factor]

/-- The analytically filled square vanishes at either complex endpoint. -/
theorem square_endpoint (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    D.square (a,ψ) = 0 := by
  rw [square,sourceAngularSelectedPolynomial_eq_endpoint_factor]
  rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl <;> simp

/-- The filled square is also independent of the Cauchy chart on the
 full overlap, including points on the cut and its endpoints. -/
theorem square_eqOn_overlap (D E : SourceAbelianCauchyChart hp hp1 j)
    (ψ : CoeffPair p) (hψD : ψ ∈ D.sources) (hψE : ψ ∈ E.sources) :
    EqOn (fun z => D.square (z,ψ)) (fun z => E.square (z,ψ))
      (ball D.center D.radius ∩ ball E.center E.radius) := by
  apply continuous_eqOn_of_dense_on_open (sourcePeriodicSegment hp hp1 ψ j)ᶜ _
    (dense_complex_segment_complement _ _) (isOpen_ball.inter isOpen_ball) _ _
    ((D.square_analytic ψ hψD).continuousOn.mono inter_subset_left)
    ((E.square_analytic ψ hψE).continuousOn.mono inter_subset_right)
  intro z hz
  change D.square (z,ψ) = E.square (z,ψ)
  rw [D.square_eq_primitive_sq ψ z hz.2,E.square_eq_primitive_sq ψ z hz.2]
  exact congrArg (fun w : ℂ => w^2) (D.primitive_eqOn_overlap E ψ hψD hψE j hz)

end NLS.ZakharovShabat.SourceAbelianCauchyChart
