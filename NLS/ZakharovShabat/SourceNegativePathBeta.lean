import NLS.ZakharovShabat.SourceAngularRightEndpointPath
import NLS.ZakharovShabat.SourceCanonicalRootReflection
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

/-! Actual paired terminal values on reflected signed gaps. The
negative path begins at the right endpoint. Both normalized primitive
boundary values are zero, and the same terminal sheet is retained. -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A reflected path evaluates the negative off-index primitive even
when the POSITIVE gap is the numerator's own index. No positive
primitive is supplied or used. -/
theorem sourceAngular_negative_pathIntegral_eq_beta
    (hp : p≠⊤) (hp1 : 1<p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (href : SourcePeriodicReflection hp hp1 ψ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ (-m)=
      -canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hw : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet (-m) ψ=
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ)
    (d : ℂ) (S : ℝ) (G J : ℂ → ℂ) (B : ℂ)
    (hJ : SourceAngularDirichletPrimitiveData hp hp1 n (-m) s ψ d S G B J)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hneg : ∀ t∈Ioo (0:ℝ) 1, -γ.extend t∈sourceAngularRegularSheetDisc hp ψ d S
      (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ))
    (hIntNeg : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ))
        (z,ψ))) (γ.map continuous_neg)) :
    sourceAngularPathIntegral n s
      (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ)) ψ
        (γ.map continuous_neg)=sourceAngularBeta hp hp1 n (-m) s ψ := by
  let κ := (γ.map continuous_neg).cast (href m).2 hμ
  have hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1) :=
    contDiff_neg.comp_contDiffOn hγ
  have hκD : ∀ t∈Ioo (0:ℝ) 1, κ.extend t∈sourceAngularRegularSheetDisc hp ψ d S
      (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet (-m) ψ) := by
    intro t ht
    rw [hw]
    exact hneg t ht
  have hκInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet (-m) ψ))
        (z,ψ))) κ := by
    rw [hw]
    exact hIntNeg.cast (href m).2 hμ
  have hminus := hJ.right_pathIntegral_eq_beta κ hκ hκD hκInt
  change sourceAngularPathIntegral n s
      (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet (-m) ψ)) ψ κ=
        sourceAngularBeta hp hp1 n (-m) s ψ at hminus
  rw [hw] at hminus
  simpa only [sourceAngularPathIntegral,κ,curveIntegral_cast] using hminus

end NLS.ZakharovShabat
