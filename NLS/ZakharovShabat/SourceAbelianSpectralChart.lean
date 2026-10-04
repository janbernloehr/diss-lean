import NLS.ZakharovShabat.SourceAbelianSpectralCompatibility

/-! # Compatible full spectral charts at complex potentials

A chart records a full spectral continuation and its actual projected
exterior values. The existence theorem supplies charts uniformly on
source balls covering an open connected almost-real neighborhood.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAbelianSpectralChart (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (ψ : CoeffPair p) where
  discs : SourceAbelianUniformDiscFamily hp hp1 W
  source_mem : ψ ∈ ball discs.source.val discs.sourceRadius
  primitive : ℤ → ℂ → ℂ
  exterior_eq : ∀ n, EqOn (primitive n) (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) discs.exterior
  analytic : ∀ n, AnalyticOnNhd ℂ (primitive n) (sourceOpenGapComplement hp hp1 ψ)
  derivative : ∀ n z, z ∈ sourceCanonicalRootDomain hp hp1 ψ →
    HasDerivAt (primitive n) (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z
  index_shift : ∀ n z, primitive n z = primitive 0 z+I*(Real.pi : ℂ)*n

namespace SourceAbelianSpectralChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {ψ : CoeffPair p}

/-- Even charts constructed in different root neighborhoods agree. -/
theorem eqOn (D : SourceAbelianSpectralChart hp hp1 W ψ) (E : SourceAbelianSpectralChart hp hp1 V ψ) (n : ℤ) :
    EqOn (D.primitive n) (E.primitive n) (sourceOpenGapComplement hp hp1 ψ) :=
  D.discs.spectral_primitives_eq E.discs ψ D.source_mem E.source_mem n (D.primitive n) (E.primitive n)
    (D.analytic n) (E.analytic n) (D.exterior_eq n) (E.exterior_eq n)

end SourceAbelianSpectralChart

/-- One analytic root neighborhood supports compatible full spectral
charts uniformly on source balls near the whole real-source locus. -/
theorem exists_sourceAbelian_almostReal_spectral_charts (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ IsOpen V ∧ IsConnected V ∧
      realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) ∧
      ∀ ψ ∈ V, ∃ D : SourceAbelianUniformDiscFamily hp hp1 W,
        ψ ∈ ball D.source.val D.sourceRadius ∧
        ∀ χ ∈ ball D.source.val D.sourceRadius,
          ∃ E : SourceAbelianSpectralChart hp hp1 W χ, E.discs = D := by
  obtain ⟨W,V,hW,hV,hconn,hreal,hVW,hD,hroot,hglobal⟩ := exists_sourceAbelian_almostReal_spectral_continuation hp hp1
  refine ⟨W,V,hW,hV,hconn,hreal,hVW,hD,hroot,?_⟩
  intro ψ hψ
  obtain ⟨D,hψD,hall⟩ := hglobal ψ hψ
  refine ⟨D,hψD,?_⟩
  intro χ hχ
  obtain ⟨F,hF⟩ := hall χ hχ
  exact ⟨{
    discs := D
    source_mem := hχ
    primitive := F
    exterior_eq := fun n => (hF n).1
    analytic := fun n => (hF n).2.1
    derivative := fun n => (hF n).2.2.1
    index_shift := fun n => (hF n).2.2.2
  },rfl⟩

end NLS.ZakharovShabat
