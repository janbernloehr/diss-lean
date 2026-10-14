import NLS.ZakharovShabat.SourceStandardRootOmittedCommonDomain

/-!
# Lemma 10.5 with its literal product and common analytic domains

Every omitted index uses the actual normalized symmetric product. The
same common source domain, local neighborhoods, disks and constants from
Lemma 10.3 support all omitted products; no further shrinking is needed.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All omitted products share the original standard-root isolating family. -/
structure SourceOmittedRootNeighborhoods (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) (c : ℝ) : Prop extends
    SourceStandardRootNeighborhoods hp hp1 V D c where
  omitted_joint : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
    ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ V)
  omitted_nonzero : ∀ ψ ∈ V, ∀ n : ℤ, ∀ z ∈ (⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ,
    sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0
  omitted_disk : ∀ ψ ∈ V, ∀ n : ℤ,
    AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ) (D n) ∧
    ∀ z ∈ D n, sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0

/-- Lemma 10.5, including actual cutoff convergence, on the unchanged common domain. -/
structure SourceLemma10_5Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  roots : SourceLemma10_3Data hp hp1 W
  spectral : ∀ ψ ∈ W, ∀ n : ℤ,
    AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n)
  joint : ∀ n : ℤ, IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
    AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n)
  locally_uniform : ∀ n : ℤ,
    TendstoLocallyUniformlyOn (sourceStandardRootOmittedPartialProduct hp hp1 n)
      (sourceStandardRootOmittedJointProduct hp hp1 n) atTop
      (sourceStandardRootOmittedJointDomain hp hp1 W n)
  nonzero : ∀ ψ : CoeffPair p, ∀ n : ℤ, ∀ z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n,
    sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0
  absolute_pairs : ∀ ψ : CoeffPair p, ∀ n : ℤ, ∀ z : ℂ,
    Summable (fun j => ‖sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j-1‖)
  cutoffs : ∀ ψ : CoeffPair p, ∀ n : ℤ, ∀ z : ℂ,
    Tendsto (fun N => sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ))
      atTop (𝓝 (sourceStandardRootOmittedProduct hp hp1 n ψ z))
  neighborhoods : ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ W ∧
    ∃ D c, SourceOmittedRootNeighborhoods hp hp1 V D c

/-- Any Lemma 10.3 common domain supports all of Lemma 10.5 without shrinking. -/
theorem SourceLemma10_3Data.omittedProducts
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_3Data hp hp1 W) (hW : IsOpen W) : SourceLemma10_5Data hp hp1 W := by
  have hs (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
      AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ)
        (sourceStandardRootOmittedDomain hp hp1 ψ n) :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 n W
      (h.omittedJoint hW n).2.1 ψ hψ
  refine ⟨h,hs,fun n => ⟨(h.omittedJoint hW n).1,(h.omittedJoint hW n).2.1⟩,
    fun n => (h.omittedJoint hW n).2.2.1,
    fun ψ n z hz => sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hz,
    fun ψ n z => summable_norm_sourceStandardRootOmittedPairedFactor_sub_one hp hp1 ψ z n,
    fun ψ n z => tendsto_sourceStandardRootOmittedPartialProduct hp hp1 n ψ z,?_⟩
  intro ψ hψ
  obtain ⟨V,hVo,hVc,hψV,hVW,D,c,hD⟩ := h.neighborhoods ψ hψ
  refine ⟨V,hVo,hVc,hψV,hVW,D,c,hD,?_,?_,?_⟩
  · intro n
    exact (h.omittedClosedFixed hW hVW hD.toSourceIsolatingNeighborhoods n).1
  · intro χ hχ n z hz
    exact (h.omittedClosedFixed hW hVW hD.toSourceIsolatingNeighborhoods n).2 (z,χ) ⟨hz,hχ⟩
  · intro χ hχ n
    have hsub := hD.toSourceIsolatingNeighborhoods.disk_subset_omittedDomain χ hχ n
    exact ⟨(hs χ (hVW hχ) n).mono hsub,
      fun z hz => sourceStandardRootOmittedProduct_ne_zero hp hp1 χ z n (hsub hz)⟩

/-- Lemma 10.5 for every finite p>1 with all earlier common-domain assertions retained. -/
theorem sourceLemma10_5 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_5Data hp hp1 W := by
  obtain ⟨W,ho,hc,hreal,h⟩ := sourceLemma10_3 hp hp1
  exact ⟨W,ho,hc,hreal,h.omittedProducts ho⟩

end NLS.ZakharovShabat
