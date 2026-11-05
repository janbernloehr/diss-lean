import NLS.ZakharovShabat.SourceAngularBeta

/-! The off-index normalized primitive vanishes at BOTH endpoints.
A reflected positive-frequency path begins at the negative gap's RIGHT
endpoint. Its integral therefore has the SAME normalized terminal value,
with no unproved basepoint correction. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual glued primitive data evaluate integrable paths starting at
the RIGHT periodic endpoint, using their proved right boundary value. -/
theorem SourceAngularSheetPrimitiveData.right_endpoint_pathIntegral_eq_value
    {hp : p≠⊤} {hp1 : 1<p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    {b : ℂ} (hb : b∈sourceAngularRegularSheetDisc hp ψ c R w)
    (γ : Path (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ c R w)
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ=E b := by
  convert curveIntegral_eq_sub_of_primitive_boundary_start _ E _ hE.hasDerivAt_sheet
    γ hγ hγD hb hInt hE.tendsto_right_sheet using 1 <;> first | rfl | simp only [sub_zero]

/-- The SAME actual Dirichlet terminal value is obtained from a path
starting at either periodic endpoint of the selected off-index gap. -/
theorem SourceAngularDirichletPrimitiveData.right_pathIntegral_eq_terminal
    {hp : p≠⊤} {hp1 : 1<p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E)
    (γ : Path (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ c R
      (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)))
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) ψ γ=
        E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) :=
  hE.primitive.right_endpoint_pathIntegral_eq_value hE.terminal_mem γ hγ hγD hInt

/-- The right-start integral is the actual chosen beta value, not just
a value of one supplied primitive. -/
theorem SourceAngularDirichletPrimitiveData.right_pathIntegral_eq_beta
    {hp : p≠⊤} {hp1 : 1<p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E)
    (γ : Path (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ c R
      (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)))
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) ψ γ=
        sourceAngularBeta hp hp1 n m s ψ :=
  (hE.right_pathIntegral_eq_terminal γ hγ hγD hInt).trans hE.beta_eq_terminal.symm

end NLS.ZakharovShabat
