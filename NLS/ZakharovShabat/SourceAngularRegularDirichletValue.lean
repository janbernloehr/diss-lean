import NLS.ZakharovShabat.SourceAngularDirichletDiscPrimitive

/-!
# The unique regular Dirichlet angular value

At an enclosed regular Dirichlet terminal, all normalized primitive
constructions give one complex value. Every integrable endpoint path
on the prescribed sheet evaluates to that value. The common-domain
theorem supplies existence simultaneously for all noncollapsed
off-diagonal pairs, under Section 13's endpoint exclusions.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Values obtained from any enclosing disc and any actual normalized
Dirichlet primitive. This does not select arbitrary values elsewhere. -/
def sourceAngularRegularDirichletValues
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Set ℂ :=
  {b | ∃ c : ℂ, ∃ R : ℝ, ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
    SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E ∧
      E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) = b}

/-- An actual normalized Dirichlet primitive evaluates integrable C¹
endpoint paths, including paths through the canonical gap interior. -/
theorem SourceAngularDirichletPrimitiveData.pathIntegral_eq_terminal
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R
      (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)))
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) ψ γ =
        E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) :=
  hE.primitive.endpoint_pathIntegral_eq_value hE.terminal_mem γ hγ hγD hInt

/-- Existence on the assigned discs gives a unique value among
constructions on every enclosing disc, not just the assigned family. -/
theorem SourceAngularDirichletDiscFamilyData.exists_unique_dirichlet_value
    {hp : p ≠ ⊤} {hp1 : 1 < p}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℤ → ℂ} {R : ℤ → ℝ}
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R) (n m : ℤ) (hmn : m ≠ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    ∃! b : ℂ, b ∈ sourceAngularRegularDirichletValues hp hp1 n m s ψ := by
  obtain ⟨F,A,E,hE⟩ := D.exists_dirichlet_primitive_data n m hmn hgap hdata hleft hright
  refine ⟨E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
    ⟨c m,R m,F,A,E,hE,rfl⟩,?_⟩
  intro b hb
  obtain ⟨d,S,G,B,J,hJ,hb⟩ := hb
  exact hb.symm.trans (hJ.terminal_eq hE)

/-- The actual psi family supplies a unique regular Dirichlet angular
value on one common open neighborhood of the whole real locus, for
every noncollapsed off-diagonal pair with the stated endpoint exclusions. -/
theorem exists_sourceAngularRegularDirichlet_values (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          ∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
              canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
            canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
              canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
            canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
              canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
            ∃! b : ℂ, b ∈ sourceAngularRegularDirichletValues hp hp1 n m s ψ := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hdata⟩ :=
    exists_sourceAngularDirichlet_common_domain hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,?_⟩
  intro ψ hψ n m hmn hgap hleft hright
  obtain ⟨hendpoint,c,R,D⟩ := hdata ψ hψ
  exact D.exists_unique_dirichlet_value n m hmn hgap (hendpoint m) hleft hright

end NLS.ZakharovShabat
