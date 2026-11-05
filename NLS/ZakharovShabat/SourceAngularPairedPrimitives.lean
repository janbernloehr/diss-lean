import NLS.ZakharovShabat.SourceAngularPairedPathBeta
import NLS.ZakharovShabat.SourceAngularOriginalBetaValues

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual endpoint-normalized primitive data for BOTH selected
signed gaps, supplied by the SAME checked original psi family. -/
structure SourceAngularPairedDirichletPrimitives (hp : p≠⊤) (hp1 : 1<p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) where
  positiveCenter : ℂ
  positiveRadius : ℝ
  positiveExterior : ℂ → ℂ
  positiveConstant : ℂ
  positivePrimitive : ℂ → ℂ
  negativeCenter : ℂ
  negativeRadius : ℝ
  negativeExterior : ℂ → ℂ
  negativeConstant : ℂ
  negativePrimitive : ℂ → ℂ
  positive_data : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ
    positiveCenter positiveRadius positiveExterior positiveConstant positivePrimitive
  negative_data : SourceAngularDirichletPrimitiveData hp hp1 n (-m) s ψ
    negativeCenter negativeRadius negativeExterior negativeConstant negativePrimitive

/-- Original all-index period normalization CONSTRUCTS both actual
primitive data at every regular pair of actual Dirichlet terminals. -/
theorem SourceLemma12_12Data.nonempty_pairedDirichletPrimitives
    {hp : p≠⊤} {hp1 : 1<p} {W₀ W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ∈W)
    (n m : ℤ) (hmn : m≠n) (hneg : -m≠n)
    (hwp : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ≠0)
    (hwn : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet (-m) ψ≠0) :
    Nonempty (SourceAngularPairedDirichletPrimitives hp hp1 n m s ψ) := by
  obtain ⟨C,hμ⟩ := H.angular_original_circles ψ hψ
  obtain ⟨F,A,E,hE⟩ := H.beta_original_dirichlet_primitive ψ hψ n m hmn (C m) (hμ m) hwp
  obtain ⟨G,B,J,hJ⟩ := H.beta_original_dirichlet_primitive ψ hψ n (-m) hneg (C (-m)) (hμ (-m)) hwn
  exact ⟨⟨(C m).center,(C m).radius,F,A,E,(C (-m)).center,(C (-m)).radius,G,B,J,hE,hJ⟩⟩

theorem SourceAngularPairedDirichletPrimitives.pathIntegral_eq_beta_pair
    {hp : p≠⊤} {hp1 : 1<p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    (D : SourceAngularPairedDirichletPrimitives hp hp1 n m s ψ)
    (href : SourcePeriodicReflection hp hp1 ψ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ (-m)=
      -canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hw : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet (-m) ψ=
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpos : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ
      D.positiveCenter D.positiveRadius (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ))
    (hneg : ∀ t∈Ioo (0:ℝ) 1, -γ.extend t∈sourceAngularRegularSheetDisc hp ψ
      D.negativeCenter D.negativeRadius (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ))
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ))
        (z,ψ))) γ)
    (hIntNeg : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ))
        (z,ψ))) (γ.map continuous_neg)) :
    sourceAngularPathIntegral n s
        (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ)) ψ γ+
      sourceAngularPathIntegral n s
        (sourceAngularRootSheet hp (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ)) ψ
          (γ.map continuous_neg)=sourceAngularBeta hp hp1 n m s ψ+sourceAngularBeta hp hp1 n (-m) s ψ :=
  sourceAngular_signed_pair_pathIntegral_eq_beta hp hp1 n m s ψ href hμ hw
    D.positiveCenter D.negativeCenter D.positiveRadius D.negativeRadius
    D.positiveExterior D.negativeExterior D.positivePrimitive D.negativePrimitive
    D.positiveConstant D.negativeConstant D.positive_data D.negative_data γ hγ hpos hneg hInt hIntNeg

end NLS.ZakharovShabat
