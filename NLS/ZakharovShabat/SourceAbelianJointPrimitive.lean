import NLS.ZakharovShabat.SourceAbelianJointChart
import NLS.ComplexAnalysis.GlueHolomorphicCharts

/-! # A single normalized joint abelian primitive near all real sources

All compatible product charts glue on their open union. This union
contains every real-source point off its spectral cuts. The resulting
jointly complex-analytic function has the actual real-source values
and the exact logarithmic differential throughout its domain.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The open union of every valid normalized abelian product chart. -/
def sourceAbelianJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (ℂ × CoeffPair p) :=
  ⋃ D : SourceAbelianJointChart hp hp1, D.domain

/-- The chart-independent normalized joint abelian primitive. Values
outside the joint domain are immaterial. -/
def sourceAbelianJointPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) : ℂ × CoeffPair p → ℂ :=
  glueHolomorphicCharts (fun D : SourceAbelianJointChart hp hp1 => D.domain) (fun D => D.toFun n)

theorem isOpen_sourceAbelianJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (sourceAbelianJointDomain hp hp1) := isOpen_iUnion (fun D => D.isOpen_domain)

/-- The glued domain avoids every source's canonical cuts. -/
theorem sourceAbelianJointDomain_subset_rootDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianJointDomain hp hp1) :
    t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2 := by
  obtain ⟨D,hD⟩ := mem_iUnion.mp ht
  exact D.root_domain t hD

/-- On every real-source slice, the joint domain is exactly the full
spectral cut complement. No spectral points off the cuts are lost. -/
theorem mem_sourceAbelianJointDomain_real_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (z : ℂ) :
    (z,φ.val) ∈ sourceAbelianJointDomain hp hp1 ↔ z ∈ sourceCanonicalRootDomain hp hp1 φ.val := by
  constructor
  · exact sourceAbelianJointDomain_subset_rootDomain hp hp1 (z,φ.val)
  · intro hz
    obtain ⟨D,hsource,hcenter⟩ := exists_sourceAbelianJointChart hp hp1 φ z hz
    apply mem_iUnion.mpr
    refine ⟨D,?_⟩
    simpa only [hsource,hcenter] using D.center_mem

/-- Every chart gives exactly the same glued values, including at
complex potentials on chart overlaps. -/
theorem sourceAbelianJointPrimitive_eq_chart (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (D : SourceAbelianJointChart hp hp1) :
    EqOn (sourceAbelianJointPrimitive hp hp1 n) (D.toFun n) D.domain :=
  glueHolomorphicCharts_eq_on _ _ (fun D E => D.eqOn_overlap E n) D

theorem sourceAbelianJointPrimitive_eventuallyEq_chart (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (D : SourceAbelianJointChart hp hp1) (t : ℂ × CoeffPair p) (ht : t ∈ D.domain) :
    sourceAbelianJointPrimitive hp hp1 n =ᶠ[𝓝 t] D.toFun n :=
  glueHolomorphicCharts_eventuallyEq _ _ (fun D => D.isOpen_domain) (fun D E => D.eqOn_overlap E n) D t ht

/-- Joint analyticity holds on the whole open union, with every
spectral and real-source anchor represented by the same function. -/
theorem sourceAbelianJointPrimitive_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceAbelianJointPrimitive hp hp1 n) (sourceAbelianJointDomain hp hp1) := by
  intro t ht
  obtain ⟨D,hD⟩ := mem_iUnion.mp ht
  exact (D.analytic n t hD).congr (sourceAbelianJointPrimitive_eventuallyEq_chart hp hp1 n D t hD).symm

/-- The glued differential is the actual discriminant differential
divided by its canonical root, also at complex sources. -/
theorem sourceAbelianJointPrimitive_hasFDerivAt (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianJointDomain hp hp1) :
    HasFDerivAt (sourceAbelianJointPrimitive hp hp1 n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  obtain ⟨D,hD⟩ := mem_iUnion.mp ht
  exact (D.hasFDerivAt n t hD).congr_of_eventuallyEq
    (sourceAbelianJointPrimitive_eventuallyEq_chart hp hp1 n D t hD)

/-- The original endpoint normalization is retained on every real
source's entire cut complement. -/
theorem sourceAbelianJointPrimitive_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAbelianJointPrimitive hp hp1 n (z,φ.val) =
      sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n := by
  obtain ⟨D,hD⟩ := mem_iUnion.mp ((mem_sourceAbelianJointDomain_real_iff hp hp1 φ z).mpr hz)
  exact (sourceAbelianJointPrimitive_eq_chart hp hp1 n D hD).trans (D.real_eq n φ hD.2 z hD.1)

/-- The signed index changes only the exact additive constant on the
entire joint domain, including all its complex-source points. -/
theorem sourceAbelianJointPrimitive_eq_zeroIndex_add (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianJointDomain hp hp1) :
    sourceAbelianJointPrimitive hp hp1 n t = sourceAbelianJointPrimitive hp hp1 0 t+I*(Real.pi : ℂ)*n := by
  obtain ⟨D,hD⟩ := mem_iUnion.mp ht
  rw [sourceAbelianJointPrimitive_eq_chart hp hp1 n D hD,sourceAbelianJointPrimitive_eq_chart hp hp1 0 D hD]
  exact sourceAbelianLogChart_eq_zeroIndex_add hp hp1 D.source.val D.source.property D.center n t

/-- Exponentiation recovers the actual joint Floquet multiplier with
the prescribed index factor. -/
theorem sourceAbelianJointPrimitive_exp (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianJointDomain hp hp1) :
    exp (sourceAbelianJointPrimitive hp hp1 n t) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t := by
  obtain ⟨D,hD⟩ := mem_iUnion.mp ht
  rw [sourceAbelianJointPrimitive_eq_chart hp hp1 n D hD]
  exact sourceAbelianLogChart_exp hp hp1 D.source.val D.source.property D.center n t
    (D.root_domain (D.center,D.source.val) D.center_mem) (D.root_domain t hD)

end NLS.ZakharovShabat
