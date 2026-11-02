import NLS.ComplexAnalysis.QuadraticCosineWeightedCancellation
import NLS.ZakharovShabat.SourceGapCosineError
import NLS.ZakharovShabat.SourcePsiCriticalRootComparison

/-! # Critical cancellation in the actual gap-cosine formula

The canonical filled square is the square of the Cauchy boundary primitive.
The quadratic Cauchy equation therefore annihilates its product with the
actual critical numerator. The proof includes endpoints and collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The cosine mean of the filled square times the actual critical numerator is zero. -/
theorem fullSquare_critical_cosineMean_eq_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (k : ℤ) :
    sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 W k t*
      sourceCriticalRootGapNumerator hp hp1 t.2 k t.1) ψ = 0 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ k
  let δ := sourceStandardRootHalfGap hp hp1 ψ k
  let H : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ)
  let g := sourceCriticalRootGapNumerator hp hp1 ψ k
  have ht (t : ℝ) : cosineGapPoint τ δ (t:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ k := by
    rw [sourcePeriodicSegment_eq_midpoint_segment]
    exact cosineGapPoint_real_mem_segment τ δ t
  have hball (t : ℝ) : cosineGapPoint τ δ (t:ℂ) ∈ ball (C.discs.center k) (C.discs.outer k) :=
    C.segment_subset_outer k ψ hψ (ht t)
  have hH (t : ℝ) : DifferentiableAt ℂ H (cosineGapPoint τ δ (t:ℂ)) :=
    (C.quotient_slice_analytic k ψ hψ _ (hball t)).differentiableAt
  obtain ⟨D⟩ := C.charts ψ hψ
  have heq (t : ℝ) : quadraticRootPolynomial τ (δ^2) (cosineGapPoint τ δ (t:ℂ))*
      deriv H (cosineGapPoint τ δ (t:ℂ))+
        (cosineGapPoint τ δ (t:ℂ)-τ)*H (cosineGapPoint τ δ (t:ℂ)) =
          g (cosineGapPoint τ δ (t:ℂ)) := by
    have he := sourceFullAbelianCauchyQuotient_equation hp hp1 W ψ k _ _
      ((C.discs.inner_pos k).trans (C.discs.inner_lt k)) D (C.circle_root k ψ hψ)
      (C.discs.avoids_other ψ hψ k) (C.extension_analytic ψ hψ k) _ (hball t)
    have hδ : δ^2 = (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2/4 := by
      dsimp [δ,sourceStandardRootHalfGap]
      ring
    simpa only [hδ,τ,H,g,sourceAngularSelectedPolynomial,sourceStandardRootMidpoint] using he
  have hg0 : AnalyticOnNhd ℂ g (sourceStandardRootOmittedDomain hp hp1 ψ k) :=
    (analyticOnNhd_const.sub analyticOnNhd_id).mul (C.extension_analytic ψ hψ k)
  have hg : Continuous (fun t : ℝ => g (cosineGapPoint τ δ (t:ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hT : ContinuousAt (fun s : ℝ => cosineGapPoint τ δ (s:ℂ)) t := by
      unfold cosineGapPoint
      fun_prop
    exact (hg0 _ (C.discs.avoids_other ψ hψ k (ball_subset_closedBall (hball t)))).continuousAt.comp (f := fun s : ℝ => cosineGapPoint τ δ (s:ℂ)) hT
  have hz := integral_quadraticCosinePrimitive_sq_mul_eq_zero τ δ H g hH heq hg
  unfold sourceGapCosineMean parametricCosineMean
  convert hz using 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [C.fullSquare_eq_gapBoundary_sq k ψ hψ t true]
  simp only [gapBoundary,↓reduceIte,quadraticCosinePrimitive,← Complex.ofReal_sin,
    ← Complex.ofReal_cos,τ,δ,H,g,cosineGapPoint]
  ring

/-- Changing the primitive's ambient source neighborhood preserves the zero mean. -/
theorem fullSquare_critical_cosineMean_eq_zero_of_chart
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    {V : Set (CoeffPair p)} (D : SourceAbelianSpectralChart hp hp1 V ψ) (k : ℤ) :
    sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 V k t*
      sourceCriticalRootGapNumerator hp hp1 t.2 k t.1) ψ = 0 := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have he : sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 V k t*
      sourceCriticalRootGapNumerator hp hp1 t.2 k t.1) ψ =
      sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 W k t*
        sourceCriticalRootGapNumerator hp hp1 t.2 k t.1) ψ := by
    unfold sourceGapCosineMean parametricCosineMean
    congr 1
    funext θ
    dsimp only
    rw [sourceFullAbelianSquare_independent_neighborhood D E]
  exact he.trans (C.fullSquare_critical_cosineMean_eq_zero ψ hψ k)

/-- The deleted critical product has the matching zero cosine mean,
with the printed -i critical-root normalization removed exactly. -/
theorem fullSquare_criticalDeleted_cosineMean_eq_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (k : ℤ) :
    sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 W k t*
      (sourceCriticalRoot hp hp1 t.2 k-t.1)*sourceCriticalDeletedQuotient hp hp1 k t.2 t.1) ψ = 0 := by
  have hz := C.fullSquare_critical_cosineMean_eq_zero ψ hψ k
  have he : sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 W k t*
      sourceCriticalRootGapNumerator hp hp1 t.2 k t.1) ψ =
      -I*sourceGapCosineMean hp hp1 k (fun t => sourceFullAbelianSquare hp hp1 W k t*
        (sourceCriticalRoot hp hp1 t.2 k-t.1)*sourceCriticalDeletedQuotient hp hp1 k t.2 t.1) ψ := by
    unfold sourceGapCosineMean parametricCosineMean
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    simp only [sourceCriticalRootGapNumerator,sourceCriticalRootRatioExtension,
      sourceCriticalDeletedQuotient,sourceCriticalRoot]
    ring
  rw [he] at hz
  exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr I_ne_zero)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
