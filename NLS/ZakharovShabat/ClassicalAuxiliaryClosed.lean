import NLS.ZakharovShabat.ClassicalAuxiliaryResolvent

/-!
# The original closed unbounded auxiliary interval operator

The partial linear map acts on the physical interval `L²` space. Its domain is
exactly the `L²` classes of original auxiliary endpoint-domain functions, and its
value is the class of their actual differential expression. A bounded two-sided
resolvent proves closedness in the physical base-space graph topology.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The graph of the original interval operator in the physical base-space product. -/
def classicalAuxiliaryOperatorGraph (b : BoundaryCondition) (u : IntervalPairL2) :
    Submodule ℂ (IntervalPairL2 × IntervalPairL2) :=
  LinearMap.range ((classicalAuxiliaryInclusion b).prod (classicalAuxiliaryOperator b u)).toLinearMap

@[simp] theorem mem_classicalAuxiliaryOperatorGraph (b : BoundaryCondition) (u x y : IntervalPairL2) :
    (x, y) ∈ classicalAuxiliaryOperatorGraph b u ↔
      ∃ f : ClassicalAuxiliaryDomain b, classicalAuxiliaryInclusion b f = x ∧ classicalAuxiliaryOperator b u f = y := by
  simp [classicalAuxiliaryOperatorGraph, LinearMap.mem_range, Prod.ext_iff]

private theorem classicalAuxiliaryOperatorGraph_fst_zero (b : BoundaryCondition) (u : IntervalPairL2)
    (v : IntervalPairL2 × IntervalPairL2) (hv : v ∈ classicalAuxiliaryOperatorGraph b u) (hz : v.1 = 0) : v.2 = 0 := by
  obtain ⟨f, hf, hL⟩ := (mem_classicalAuxiliaryOperatorGraph b u v.1 v.2).mp hv
  have hf0 : f = 0 := classicalAuxiliaryInclusion_injective b (hf.trans (hz.trans (map_zero _).symm))
  simpa only [hf0, map_zero] using hL.symm

/-- The original unbounded operator with its domain inside physical `L²[0,1]`. -/
def classicalAuxiliaryUnboundedOperator (b : BoundaryCondition) (u : IntervalPairL2) :
    IntervalPairL2 →ₗ.[ℂ] IntervalPairL2 := (classicalAuxiliaryOperatorGraph b u).toLinearPMap

@[simp] theorem classicalAuxiliaryUnboundedOperator_graph (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalAuxiliaryUnboundedOperator b u).graph = classicalAuxiliaryOperatorGraph b u :=
  Submodule.toLinearPMap_graph_eq _ (classicalAuxiliaryOperatorGraph_fst_zero b u)

/-- The domain is precisely the included original auxiliary endpoint space. -/
@[simp] theorem mem_classicalAuxiliaryUnboundedOperator_domain (b : BoundaryCondition) (u x : IntervalPairL2) :
    x ∈ (classicalAuxiliaryUnboundedOperator b u).domain ↔
      ∃ f : ClassicalAuxiliaryDomain b, classicalAuxiliaryInclusion b f = x := by
  rw [LinearPMap.mem_domain_iff, classicalAuxiliaryUnboundedOperator_graph]
  simp only [mem_classicalAuxiliaryOperatorGraph]
  constructor
  · rintro ⟨y, f, hf, _⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨classicalAuxiliaryOperator b u f, f, rfl, rfl⟩

/-- The domain description uses actual `H¹` functions and the original auxiliary endpoint equations. -/
theorem mem_classicalAuxiliaryUnboundedOperator_domain_iff_original (b : BoundaryCondition) (u x : IntervalPairL2) :
    x ∈ (classicalAuxiliaryUnboundedOperator b u).domain ↔
      ∃ (f : ℝ → ℂ × ℂ) (_hf : HasClassicalAuxiliaryDomain b f)
        (hL : MemLp f 2 (volume.restrict (Ioc 0 1))), intervalL2OfFunction f hL = x := by
  rw [mem_classicalAuxiliaryUnboundedOperator_domain]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨classicalAuxiliaryDomainRepresentative b f, classicalAuxiliaryDomainRepresentative_mem b f,
      memLp_classicalAuxiliaryDomainRepresentative b f, (classicalAuxiliaryInclusion_representative b f).symm.trans hf⟩
  · rintro ⟨f, hf, hL, hx⟩
    exact ⟨classicalAuxiliaryDomainOfFunction b f hf, (classicalAuxiliaryInclusion_ofFunction b f hf hL).trans hx⟩

/-- The unbounded domain is independent of the potential. -/
theorem classicalAuxiliaryUnboundedOperator_domain (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalAuxiliaryUnboundedOperator b u).domain = (classicalAuxiliaryInclusion b).toLinearMap.range := by
  ext x
  exact mem_classicalAuxiliaryUnboundedOperator_domain b u x

/-- The original operator is densely defined in physical `L²`. -/
theorem classicalAuxiliaryUnboundedOperator_dense_domain (b : BoundaryCondition) (u : IntervalPairL2) :
    Dense ((classicalAuxiliaryUnboundedOperator b u).domain : Set IntervalPairL2) := by
  rw [classicalAuxiliaryUnboundedOperator_domain]
  exact classicalAuxiliaryInclusion_denseRange b

/-- Evaluation agrees with the classical-domain operator. -/
theorem classicalAuxiliaryUnboundedOperator_apply_inclusion (b : BoundaryCondition) (u : IntervalPairL2)
    (f : ClassicalAuxiliaryDomain b) (hf : classicalAuxiliaryInclusion b f ∈ (classicalAuxiliaryUnboundedOperator b u).domain) :
    classicalAuxiliaryUnboundedOperator b u ⟨classicalAuxiliaryInclusion b f, hf⟩ = classicalAuxiliaryOperator b u f := by
  symm
  rw [LinearPMap.image_iff hf, classicalAuxiliaryUnboundedOperator_graph, mem_classicalAuxiliaryOperatorGraph]
  exact ⟨f, rfl, rfl⟩

/-- On original representatives, the partial operator is exactly the stated differential expression. -/
theorem classicalAuxiliaryUnboundedOperator_apply_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f)
    (hL : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hx : intervalL2OfFunction f hL ∈ (classicalAuxiliaryUnboundedOperator b (intervalL2OfFunction φ hφ)).domain) :
    classicalAuxiliaryUnboundedOperator b (intervalL2OfFunction φ hφ) ⟨intervalL2OfFunction f hL, hx⟩ =
      intervalL2OfFunction (physicalOperator φ f) (memLp_classicalAuxiliaryOperator_ofFunction b φ f hφ hf) := by
  symm
  rw [LinearPMap.image_iff hx, classicalAuxiliaryUnboundedOperator_graph, mem_classicalAuxiliaryOperatorGraph]
  exact ⟨classicalAuxiliaryDomainOfFunction b f hf, classicalAuxiliaryInclusion_ofFunction b f hf hL,
    classicalAuxiliaryOperator_ofFunction b φ f hφ hf⟩

/-- A two-sided physical resolvent recognizes graph points using only base-space data. -/
theorem mem_classicalAuxiliaryOperatorGraph_iff_resolvent (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalAuxiliaryResolventSet b u) (x y : IntervalPairL2) :
    (x, y) ∈ classicalAuxiliaryOperatorGraph b u ↔ classicalAuxiliaryResolvent b u z (z • x - y) = x := by
  rw [mem_classicalAuxiliaryOperatorGraph]
  constructor
  · rintro ⟨f, rfl, rfl⟩
    change classicalAuxiliaryInclusion b (classicalAuxiliaryResolventToDomain b u z (classicalAuxiliaryPencil b u z f)) = classicalAuxiliaryInclusion b f
    rw [classicalAuxiliaryResolventToDomain_pencil b u z hz]
  · intro h
    refine ⟨classicalAuxiliaryResolventToDomain b u z (z • x - y), h, ?_⟩
    have he := classicalAuxiliaryPencil_resolventToDomain b u z hz (z • x - y)
    rw [classicalAuxiliaryPencil_apply] at he
    change classicalAuxiliaryInclusion b (classicalAuxiliaryResolventToDomain b u z (z • x - y)) = x at h
    rw [h] at he
    exact sub_right_inj.mp he

/-- The original graph is closed in the physical base-space topology. -/
theorem isClosed_classicalAuxiliaryOperatorGraph (b : BoundaryCondition) (u : IntervalPairL2) :
    IsClosed (classicalAuxiliaryOperatorGraph b u : Set (IntervalPairL2 × IntervalPairL2)) := by
  obtain ⟨z, hz⟩ := classicalAuxiliaryResolventSet_nonempty b u
  have he : (classicalAuxiliaryOperatorGraph b u : Set (IntervalPairL2 × IntervalPairL2)) =
      {v | classicalAuxiliaryResolvent b u z (z • v.1 - v.2) = v.1} := by
    ext v
    exact mem_classicalAuxiliaryOperatorGraph_iff_resolvent b u z hz v.1 v.2
  rw [he]
  exact isClosed_eq ((classicalAuxiliaryResolvent b u z).continuous.comp
    ((continuous_fst.const_smul z).sub continuous_snd)) continuous_fst

/-- The original interval Zakharov–Shabat operator is closed for every physical `L²` potential. -/
theorem classicalAuxiliaryUnboundedOperator_isClosed (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalAuxiliaryUnboundedOperator b u).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [classicalAuxiliaryUnboundedOperator_graph]
  exact isClosed_classicalAuxiliaryOperatorGraph b u

end NLS.ZakharovShabat.BoundaryCondition
