import NLS.ZakharovShabat.SourceOmittedProductBoundaryNormalization
import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood

/-! # Analytic omitted-product samples on one source neighborhood

All actual boundary-root samples are analytic and nonzero on one complex neighborhood of each real source.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real source, all actual boundary roots avoid every unselected
gap, and their omitted-product samples are simultaneously analytic and
nonzero. Both boundary conditions and all signed indices share one set. -/
theorem exists_local_source_omitted_boundary_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U,
      ∀ θ : BoundaryCondition, ∀ n : ℤ,
        canonicalPeriodOneBoundaryRoots hp hp1 θ ψ n ∈
          sourceStandardRootOmittedDomain hp hp1 ψ n ∧
        AnalyticAt ℂ (fun χ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n χ
          (canonicalPeriodOneBoundaryRoots hp hp1 θ χ n)) ψ ∧
        sourceStandardRootOmittedProduct hp hp1 n ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 θ ψ n) ≠ 0 := by
  obtain ⟨N,ε,_,_,V,hV,_,hφV,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  obtain ⟨B,hB,hφB,hroots⟩ := exists_local_source_allBoundaryRoots_analytic hp hp1 φ hφ
  obtain ⟨W,hW,_,hrealW,hproduct⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  refine ⟨V ∩ (B ∩ W),hV.inter (hB.inter hW),⟨hφV,hφB,hrealW hφ⟩,?_⟩
  intro ψ hψ θ n
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 θ ψ n
  have hμ : μ ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
    apply hcluster ψ hψ.1 n
    cases θ with
    | dirichlet => exact Or.inr (Or.inr (Or.inl rfl))
    | neumann => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have havoid : μ ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    intro m hmn hm
    have hm' := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε m
      (hcluster ψ hψ.1 m) hm
    exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hmn)) hμ hm'
  refine ⟨havoid,?_,sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ n havoid⟩
  exact ((hproduct n).2.1 (μ,ψ) ⟨hψ.2.2,havoid⟩).comp
    (f := fun χ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 θ χ n,χ))
    ((hroots θ n ψ hψ.2.1).prod analyticAt_id)

end NLS.ZakharovShabat
