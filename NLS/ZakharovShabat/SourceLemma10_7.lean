import NLS.ZakharovShabat.SourceCanonicalRootBoundaryDomain
import NLS.ZakharovShabat.SourceCorollary10_6
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# Lemma 10.7 with equations (2.13) and (2.14)

The same W and the same local V, disks and distance constant support
the canonical root. Corollary 10.6 is retained, together with exact
product normalization, analytic domains and closed-gap boundary data.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original local data with both the printed domain and fixed-source collapsed extension. -/
structure SourceCanonicalRootNeighborhoods (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) (c : ℝ) : Prop extends
    SourceSingleRootQuotientNeighborhoods hp hp1 V D c where
  canonical_joint : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
    ((⋃ m : ℤ, closure (D m))ᶜ ×ˢ V)
  collapsed : ∀ ψ ∈ V, ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 ψ) (D n)
  boundary : ∀ ψ ∈ V, ∀ n : ℤ, SourceCanonicalRootBoundaryData hp hp1 ψ n

/-- Main data retain Corollary 10.6 and the normalizations of (2.13). -/
structure SourceLemma10_7Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceCorollary10_6Data hp hp1 W
  spectral : ∀ ψ : CoeffPair p,
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 ψ) (sourceCanonicalRootDomain hp hp1 ψ)
  joint : IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
    AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W)
  locally_uniform : TendstoLocallyUniformlyOn
    (fun N (q : ℂ × CoeffPair p) => sourceCanonicalRootPartialProduct hp hp1 N q.2 q.1)
    (sourceCanonicalRootJointProduct hp hp1) atTop (sourceCanonicalRootJointDomain hp hp1 W)
  pointwise : ∀ ψ : CoeffPair p, ∀ z : ℂ,
    Tendsto (fun N => sourceCanonicalRootPartialProduct hp hp1 N ψ z) atTop
      (𝓝 (sourceCanonicalRoot hp hp1 ψ z))
  factorization : ∀ ψ : CoeffPair p, ∀ n : ℤ, ∀ z : ℂ,
    sourceCanonicalRoot hp hp1 ψ z =
      2*Complex.I*sourceStandardRoot hp hp1 ψ n z*sourceStandardRootOmittedProduct hp hp1 n ψ z
  square : ∀ ψ : CoeffPair p, ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
    (sourceCanonicalRoot hp hp1 ψ z)^2 = (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4
  nonzero : ∀ ψ : CoeffPair p, ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
    sourceCanonicalRoot hp hp1 ψ z ≠ 0
  neighborhoods : ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ W ∧
    ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c

theorem SourceCorollary10_6Data.canonicalRoots
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceCorollary10_6Data hp hp1 W) : SourceLemma10_7Data hp hp1 W := by
  refine ⟨h,sourceCanonicalRoot_analyticOnNhd hp hp1,h.roots.canonicalJoint,
    h.roots.canonicalLocallyUniform,tendsto_sourceCanonicalRootPartialProduct hp hp1,
    fun ψ n z => sourceCanonicalRoot_eq_omitted hp hp1 n ψ z,
    sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1,
    sourceCanonicalRoot_ne_zero_off_gaps hp hp1,?_⟩
  intro ψ hψ
  obtain ⟨V,ho,hc,hψV,hVW,D,c,hD⟩ := h.neighborhoods ψ hψ
  exact ⟨V,ho,hc,hψV,hVW,D,c,hD,
    h.roots.canonicalClosedFixed hVW hD.toSourceIsolatingNeighborhoods,
    h.roots.canonicalCollapsedDisk hVW hD.toSourceIsolatingNeighborhoods,
    fun χ hχ n => h.roots.canonicalBoundaryData χ (hVW hχ) n⟩

theorem sourceLemma10_7 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_7Data hp hp1 W := by
  obtain ⟨W,ho,hc,hreal,h⟩ := sourceCorollary10_6 hp hp1
  exact ⟨W,ho,hc,hreal,h.canonicalRoots⟩

end NLS.ZakharovShabat
