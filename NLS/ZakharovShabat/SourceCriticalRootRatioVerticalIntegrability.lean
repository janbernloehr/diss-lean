import NLS.ZakharovShabat.SourceCriticalRootRatioTransverseBound

/-!
# Integrability of vertically displaced gap pullbacks

For a real-type source, every periodic gap is real. A nonzero vertical
shift of the selected gap therefore stays in the full root domain.
The critical-root quotient pulled back along such a shift is
continuous and interval integrable, including after multiplication by
the cosine-path Jacobian.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every nonzero vertical shift of a real-type gap point avoids all
periodic gap segments, with no restriction on the longitudinal
parameter. -/
theorem sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (t y : ℝ) (hy : y ≠ 0) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I ∈
      sourceCanonicalRootDomain hp hp1 ψ := by
  have hpoint : (sourceCanonicalRootGapPoint hp hp1 ψ n t).im = 0 := by
    rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n t]
    simp
  have hzim : (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I).im = y := by
    simp [hpoint]
  intro m hmem
  have hzero := sourcePeriodicSegment_im_eq_zero_of_realType
    hp hp1 ψ hreal m _ hmem
  exact hy (by linarith)

/-- The full quotient along a nonzero vertical shift is a continuous
function of the signed gap parameter. -/
theorem sourceCriticalRootRatio_vertical_continuous
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun t : ℝ =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) /
      sourceCanonicalRoot hp hp1 ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I)) := by
  have hpath : Continuous (fun t : ℝ =>
      sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) := by
    unfold sourceCanonicalRootGapPoint
    fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  exact ContinuousAt.comp
    (f := fun s : ℝ => sourceCanonicalRootGapPoint hp hp1 ψ n s + (y:ℂ)*I)
    ((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ _
      (sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
        hp hp1 ψ hreal n t y hy)).continuousAt)
    hpath.continuousAt

/-- The cosine-weighted quotient on a vertically displaced real gap
is interval integrable through both longitudinal endpoints. -/
theorem sourceCriticalRootRatio_vertical_cosineWeighted_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (y : ℝ) (hy : y ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ =>
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) /
          sourceCanonicalRoot hp hp1 ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I)) *
          (sourceStandardRootHalfGap hp hp1 ψ n *
            (Real.sqrt (1-t^2):ℂ)))
      volume (-1) 1 := by
  have hweight : Continuous (fun t : ℝ =>
      sourceStandardRootHalfGap hp hp1 ψ n *
        (Real.sqrt (1-t^2):ℂ)) := by
    fun_prop
  exact Continuous.intervalIntegrable
    ((sourceCriticalRootRatio_vertical_continuous
      hp hp1 ψ hreal n y hy).mul hweight) _ _

end NLS.ZakharovShabat
