import NLS.ZakharovShabat.UniformResolvent
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The closed, densely defined Zakharov–Shabat operator

The domain-to-base operator is realized as a partial linear map on the base
coefficient space. Its domain is exactly the included one-derivative space.
A bounded two-sided spectral inverse identifies its graph with a closed set.
This proves the closedness assertion of Chapter 1, §3, printed page 23, for all
finite Banach exponents, without a smallness assumption on the potential.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The graph in the product of two copies of the base coefficient space. -/
def operatorGraph (hp : p ≠ ⊤) (φ : PairSpace p) :
    Submodule ℂ (PairSpace p × PairSpace p) :=
  LinearMap.range (domainInclusion.prod (operator hp φ)).toLinearMap

@[simp] theorem mem_operatorGraph (hp : p ≠ ⊤) (φ : PairSpace p)
    (x y : PairSpace p) :
    (x, y) ∈ operatorGraph hp φ ↔
      ∃ f : Domain p, domainInclusion f = x ∧ operator hp φ f = y := by
  simp [operatorGraph, LinearMap.mem_range, Prod.ext_iff]

private theorem operatorGraph_fst_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (v : PairSpace p × PairSpace p) (hv : v ∈ operatorGraph hp φ)
    (hzero : v.1 = 0) : v.2 = 0 := by
  obtain ⟨f, hf, hL⟩ := (mem_operatorGraph hp φ v.1 v.2).mp hv
  have hf0 : f = 0 := domainInclusion_injective (hf.trans (hzero.trans (map_zero _).symm))
  simpa only [hf0, map_zero] using hL.symm

/-- The unbounded realization of `operator`, with its actual domain inside the base space. -/
def unboundedOperator (hp : p ≠ ⊤) (φ : PairSpace p) :
    PairSpace p →ₗ.[ℂ] PairSpace p :=
  (operatorGraph hp φ).toLinearPMap

@[simp] theorem unboundedOperator_graph (hp : p ≠ ⊤) (φ : PairSpace p) :
    (unboundedOperator hp φ).graph = operatorGraph hp φ :=
  Submodule.toLinearPMap_graph_eq _ (operatorGraph_fst_zero hp φ)

/-- Membership in the partial map's domain is precisely one-derivative regularity. -/
@[simp] theorem mem_unboundedOperator_domain (hp : p ≠ ⊤) (φ : PairSpace p)
    (x : PairSpace p) :
    x ∈ (unboundedOperator hp φ).domain ↔ ∃ f : Domain p, domainInclusion f = x := by
  rw [LinearPMap.mem_domain_iff, unboundedOperator_graph]
  simp only [mem_operatorGraph]
  constructor
  · rintro ⟨y, f, hf, _⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨operator hp φ f, f, rfl, rfl⟩

/-- The domain is independent of the potential. -/
theorem unboundedOperator_domain (hp : p ≠ ⊤) (φ : PairSpace p) :
    (unboundedOperator hp φ).domain = LinearMap.range domainInclusion.toLinearMap := by
  ext x
  exact mem_unboundedOperator_domain hp φ x

/-- Evaluation agrees with the already constructed domain-to-base operator. -/
@[simp] theorem unboundedOperator_apply_inclusion (hp : p ≠ ⊤) (φ : PairSpace p)
    (f : Domain p) (hf : domainInclusion f ∈ (unboundedOperator hp φ).domain) :
    unboundedOperator hp φ ⟨domainInclusion f, hf⟩ = operator hp φ f := by
  symm
  rw [LinearPMap.image_iff hf, unboundedOperator_graph, mem_operatorGraph]
  exact ⟨f, rfl, rfl⟩

/-- The unbounded operator is densely defined for every finite Banach exponent. -/
theorem unboundedOperator_dense_domain (hp : p ≠ ⊤) (φ : PairSpace p) :
    Dense ((unboundedOperator hp φ).domain : Set (PairSpace p)) := by
  rw [unboundedOperator_domain]
  exact domainInclusion_denseRange hp

/-- A two-sided inverse recognizes graph points by an equation in the base space. -/
theorem mem_operatorGraph_iff_inverse (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (R : PairSpace p →L[ℂ] Domain p)
    (hleft : ∀ a, spectralPencil hp φ z (R a) = a)
    (hright : ∀ f, R (spectralPencil hp φ z f) = f)
    (x y : PairSpace p) :
    (x, y) ∈ operatorGraph hp φ ↔ domainInclusion (R (z • x - y)) = x := by
  rw [mem_operatorGraph]
  constructor
  · rintro ⟨f, rfl, rfl⟩
    change domainInclusion (R (spectralPencil hp φ z f)) = domainInclusion f
    rw [hright]
  · intro h
    refine ⟨R (z • x - y), h, ?_⟩
    have hP := hleft (z • x - y)
    rw [spectralPencil_apply, h] at hP
    exact sub_right_inj.mp hP

/-- The graph is closed in the base-space product topology. -/
theorem isClosed_operatorGraph (hp : p ≠ ⊤) (φ : PairSpace p) :
    IsClosed (operatorGraph hp φ : Set (PairSpace p × PairSpace p)) := by
  obtain ⟨z, R, hleft, hright, _⟩ := exists_compact_inverse hp φ
  have hgraph : (operatorGraph hp φ : Set (PairSpace p × PairSpace p)) =
      {v | domainInclusion (R (z • v.1 - v.2)) = v.1} := by
    ext v
    exact mem_operatorGraph_iff_inverse hp φ z R hleft hright v.1 v.2
  rw [hgraph]
  exact isClosed_eq
    (domainInclusion.continuous.comp
      (R.continuous.comp ((continuous_fst.const_smul z).sub continuous_snd)))
    continuous_fst

/-- The coefficient-space Zakharov–Shabat operator is closed, with no restriction
on the size of the potential. -/
theorem unboundedOperator_isClosed (hp : p ≠ ⊤) (φ : PairSpace p) :
    (unboundedOperator hp φ).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [unboundedOperator_graph]
  exact isClosed_operatorGraph hp φ

/-- If domain vectors and their images converge in the base norm, their limits
still belong to the graph. No convergence in the stronger domain norm is assumed. -/
theorem exists_domain_of_tendsto (hp : p ≠ ⊤) (φ : PairSpace p)
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → Domain p) {x y : PairSpace p}
    (hx : Filter.Tendsto (fun i => domainInclusion (f i)) l (nhds x))
    (hy : Filter.Tendsto (fun i => operator hp φ (f i)) l (nhds y)) :
    ∃ g : Domain p, domainInclusion g = x ∧ operator hp φ g = y := by
  apply (mem_operatorGraph hp φ x y).mp
  apply (isClosed_operatorGraph hp φ).mem_of_tendsto (hx.prodMk_nhds hy)
  exact Filter.Eventually.of_forall fun i =>
    (mem_operatorGraph hp φ _ _).mpr ⟨f i, rfl, rfl⟩

end NLS.ZakharovShabat
