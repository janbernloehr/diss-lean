import NLS.ZakharovShabat.SourceAngularCanonicalCosinePrimitive

/-!
# Canonical cosine primitives on the actual beta construction domain

One common open source neighborhood contains every real source, supports
both analytic boundary-coordinate sequences and all constructed beta values,
and supplies canonical cosine charts near every open real gap. The original
simply connected psi extension and its estimates are retained separately.
The local charts and endpoint-normalized primitives are constructed from
the actual spectral data; no choice of midpoint, gap, or primitive is input.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual beta values, analytic moving boundary roots, and canonical
joint cosine primitive charts coexist. Every open gap at every real source
has one local chart for all numerator indices, retaining the assigned discs
and their exact contour periods. -/
theorem exists_sourceAngularBeta_common_domain_with_canonicalCosinePrimitives
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
              canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ,
                b = sourceAngularBeta hp hp1 n m s ψ) ∧
          ∀ φ : realTypeSourceLocus p, ∀ m : ℤ,
            canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
              (periodOnePotential_mem φ.val) m ≠ 0 →
            ∃ V : Set (CoeffPair p), ∃ Ω : Set ℂ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
              φ.val ∈ V ∧ SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R := by
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,hs,hroots,hbeta⟩ :=
    exists_sourceAngularBeta_common_domain_with_analyticBoundaryRoots hp hp1
  obtain ⟨A,hA,_,hAreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let W := B ∩ A
  have hW : IsOpen W := hB.inter hA
  have hWreal : realTypeSourceLocus p ⊆ W := fun φ hφ => ⟨hBreal hφ,hAreal hφ⟩
  have hWW₀ : W ⊆ W₀ := fun φ hφ => hBW₀ hφ.1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,
    (fun b m ψ hψ => hroots b m ψ hψ.1),
    (fun ψ hψ => hbeta ψ hψ.1),?_⟩
  intro φ m hgap
  have hsub : sourceStandardRootOmittedJointDomain hp hp1 W m ⊆
      sourceStandardRootOmittedJointDomain hp hp1 A m := fun t ht => ⟨ht.1.2,ht.2⟩
  have heq : sourceStandardRootOmittedJointDomain hp hp1 W m =
      sourceStandardRootOmittedJointDomain hp hp1 A m ∩ (univ ×ˢ B) := by
    ext t
    exact ⟨fun ht => ⟨⟨ht.1.2,ht.2⟩,mem_univ _,ht.1.1⟩,
      fun ht => ⟨⟨ht.2.2,ht.1.1⟩,ht.1.2⟩⟩
  have hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m) := by
    rw [heq]
    exact (hprod m).1.inter (isOpen_univ.prod hB)
  exact hs.toSourcePsiIsolatingComplexExtension.exists_local_canonical_cosine_angular_primitives
    W hW hWW₀ φ.val (hWreal φ.property) φ.property m hgap hD ((hprod m).2.1.mono hsub)

end NLS.ZakharovShabat
