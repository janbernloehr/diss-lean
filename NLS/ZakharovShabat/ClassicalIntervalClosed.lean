import NLS.ZakharovShabat.ClassicalIntervalResolvent

/-!
# The original closed unbounded interval operator

The partial linear map acts on the physical interval `L²` space. Its domain is
exactly the `L²` classes of original classical endpoint-domain functions, and its
value is the class of their actual differential expression. A bounded two-sided
resolvent proves closedness in the physical base-space graph topology.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The graph of the original interval operator in the physical base-space product. -/
def classicalOperatorGraph (b : BoundaryCondition) (u : IntervalPairL2) :
    Submodule ℂ (IntervalPairL2 × IntervalPairL2) :=
  LinearMap.range ((classicalInclusion b).prod (classicalOperator b u)).toLinearMap

@[simp] theorem mem_classicalOperatorGraph (b : BoundaryCondition) (u x y : IntervalPairL2) :
    (x, y) ∈ classicalOperatorGraph b u ↔
      ∃ f : ClassicalIntervalDomain b, classicalInclusion b f = x ∧ classicalOperator b u f = y := by
  simp [classicalOperatorGraph, LinearMap.mem_range, Prod.ext_iff]

private theorem classicalOperatorGraph_fst_zero (b : BoundaryCondition) (u : IntervalPairL2)
    (v : IntervalPairL2 × IntervalPairL2) (hv : v ∈ classicalOperatorGraph b u) (hz : v.1 = 0) : v.2 = 0 := by
  obtain ⟨f, hf, hL⟩ := (mem_classicalOperatorGraph b u v.1 v.2).mp hv
  have hf0 : f = 0 := classicalInclusion_injective b (hf.trans (hz.trans (map_zero _).symm))
  simpa only [hf0, map_zero] using hL.symm

/-- The original unbounded operator with its domain inside physical `L²[0,1]`. -/
def classicalUnboundedOperator (b : BoundaryCondition) (u : IntervalPairL2) :
    IntervalPairL2 →ₗ.[ℂ] IntervalPairL2 := (classicalOperatorGraph b u).toLinearPMap

@[simp] theorem classicalUnboundedOperator_graph (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalUnboundedOperator b u).graph = classicalOperatorGraph b u :=
  Submodule.toLinearPMap_graph_eq _ (classicalOperatorGraph_fst_zero b u)

/-- The domain is precisely the included original classical endpoint space. -/
@[simp] theorem mem_classicalUnboundedOperator_domain (b : BoundaryCondition) (u x : IntervalPairL2) :
    x ∈ (classicalUnboundedOperator b u).domain ↔
      ∃ f : ClassicalIntervalDomain b, classicalInclusion b f = x := by
  rw [LinearPMap.mem_domain_iff, classicalUnboundedOperator_graph]
  simp only [mem_classicalOperatorGraph]
  constructor
  · rintro ⟨y, f, hf, _⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨classicalOperator b u f, f, rfl, rfl⟩

/-- The domain description uses actual `H¹` functions and the original equal/opposite endpoints. -/
theorem mem_classicalUnboundedOperator_domain_iff_original (b : BoundaryCondition) (u x : IntervalPairL2) :
    x ∈ (classicalUnboundedOperator b u).domain ↔
      ∃ (f : ℝ → ℂ × ℂ) (_hf : HasClassicalIntervalDomain b f)
        (hL : MemLp f 2 (volume.restrict (Ioc 0 1))), intervalL2OfFunction f hL = x := by
  rw [mem_classicalUnboundedOperator_domain]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨classicalDomainRepresentative b f, classicalDomainRepresentative_mem b f,
      memLp_classicalDomainRepresentative b f, (classicalInclusion_representative b f).symm.trans hf⟩
  · rintro ⟨f, hf, hL, hx⟩
    exact ⟨classicalDomainOfFunction b f hf, (classicalInclusion_ofFunction b f hf hL).trans hx⟩

/-- The unbounded domain is independent of the potential. -/
theorem classicalUnboundedOperator_domain (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalUnboundedOperator b u).domain = (classicalInclusion b).toLinearMap.range := by
  ext x
  exact mem_classicalUnboundedOperator_domain b u x

/-- The original operator is densely defined in physical `L²`. -/
theorem classicalUnboundedOperator_dense_domain (b : BoundaryCondition) (u : IntervalPairL2) :
    Dense ((classicalUnboundedOperator b u).domain : Set IntervalPairL2) := by
  rw [classicalUnboundedOperator_domain]
  exact classicalInclusion_denseRange b

/-- Evaluation agrees with the classical-domain operator. -/
theorem classicalUnboundedOperator_apply_inclusion (b : BoundaryCondition) (u : IntervalPairL2)
    (f : ClassicalIntervalDomain b) (hf : classicalInclusion b f ∈ (classicalUnboundedOperator b u).domain) :
    classicalUnboundedOperator b u ⟨classicalInclusion b f, hf⟩ = classicalOperator b u f := by
  symm
  rw [LinearPMap.image_iff hf, classicalUnboundedOperator_graph, mem_classicalOperatorGraph]
  exact ⟨f, rfl, rfl⟩

/-- On original representatives, the partial operator is exactly the stated differential expression. -/
theorem classicalUnboundedOperator_apply_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f)
    (hL : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hx : intervalL2OfFunction f hL ∈ (classicalUnboundedOperator b (intervalL2OfFunction φ hφ)).domain) :
    classicalUnboundedOperator b (intervalL2OfFunction φ hφ) ⟨intervalL2OfFunction f hL, hx⟩ =
      intervalL2OfFunction (physicalOperator φ f) (memLp_classicalOperator_ofFunction b φ f hφ hf) := by
  symm
  rw [LinearPMap.image_iff hx, classicalUnboundedOperator_graph, mem_classicalOperatorGraph]
  exact ⟨classicalDomainOfFunction b f hf, classicalInclusion_ofFunction b f hf hL,
    classicalOperator_ofFunction b φ f hφ hf⟩

/-- A two-sided physical resolvent recognizes graph points using only base-space data. -/
theorem mem_classicalOperatorGraph_iff_resolvent (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalResolventSet b u) (x y : IntervalPairL2) :
    (x, y) ∈ classicalOperatorGraph b u ↔ classicalResolvent b u z (z • x - y) = x := by
  rw [mem_classicalOperatorGraph]
  constructor
  · rintro ⟨f, rfl, rfl⟩
    change classicalInclusion b (classicalResolventToDomain b u z (classicalPencil b u z f)) = classicalInclusion b f
    rw [classicalResolventToDomain_classicalPencil b u z hz]
  · intro h
    refine ⟨classicalResolventToDomain b u z (z • x - y), h, ?_⟩
    have he := classicalPencil_classicalResolventToDomain b u z hz (z • x - y)
    rw [classicalPencil_apply] at he
    change classicalInclusion b (classicalResolventToDomain b u z (z • x - y)) = x at h
    rw [h] at he
    exact sub_right_inj.mp he

/-- The original graph is closed in the physical base-space topology. -/
theorem isClosed_classicalOperatorGraph (b : BoundaryCondition) (u : IntervalPairL2) :
    IsClosed (classicalOperatorGraph b u : Set (IntervalPairL2 × IntervalPairL2)) := by
  obtain ⟨z, hz⟩ := classicalResolventSet_nonempty b u
  have he : (classicalOperatorGraph b u : Set (IntervalPairL2 × IntervalPairL2)) =
      {v | classicalResolvent b u z (z • v.1 - v.2) = v.1} := by
    ext v
    exact mem_classicalOperatorGraph_iff_resolvent b u z hz v.1 v.2
  rw [he]
  exact isClosed_eq ((classicalResolvent b u z).continuous.comp
    ((continuous_fst.const_smul z).sub continuous_snd)) continuous_fst

/-- The original interval Zakharov–Shabat operator is closed for every physical `L²` potential. -/
theorem classicalUnboundedOperator_isClosed (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalUnboundedOperator b u).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [classicalUnboundedOperator_graph]
  exact isClosed_classicalOperatorGraph b u

end NLS.ZakharovShabat.BoundaryCondition
