import NLS.ZakharovShabat.SourceLemma10_3
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-!
# Omitted products on the unchanged common source domain

The actual symmetric cutoffs converge locally uniformly on the moving-gap
complement. The common source domain and each fixed isolating family from
Lemma 10.3 are retained, including the source's closed-disk domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint analyticity, nonvanishing and local uniform cutoff convergence on the unchanged common domain. -/
theorem SourceLemma10_3Data.omittedJoint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_3Data hp hp1 W) (hW : IsOpen W) (n : ℤ) :
    IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
    AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
    TendstoLocallyUniformlyOn (sourceStandardRootOmittedPartialProduct hp hp1 n)
      (sourceStandardRootOmittedJointProduct hp hp1 n) atTop
      (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
    ∀ q ∈ sourceStandardRootOmittedJointDomain hp hp1 W n,
      sourceStandardRootOmittedJointProduct hp hp1 n q ≠ 0 := by
  have hA (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ) :
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) m) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) m)^2) ψ :=
    ⟨h.symmetric.midpoint m ψ hψ,h.symmetric.squared_gap m ψ hψ⟩
  obtain ⟨ho,ha⟩ := sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric hp hp1 W hW hA n
  refine ⟨ho,ha,?_,fun q hq => sourceStandardRootOmittedProduct_ne_zero hp hp1 q.2 q.1 n hq.2⟩
  intro u hu q hq
  obtain ⟨U,hUo,hqU,hconv⟩ := exists_local_uniform_sourceStandardRootOmittedProduct hp hp1 n q.2 q.1
    (fun N => (sourceStandardRootOmittedPartialProduct_analyticAt_of_symmetric hp hp1 W hA n N q hq).continuousAt)
  exact ⟨U,mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hqU),hconv u hu⟩

/-- Joint analyticity and nonvanishing outside the fixed open disks, including their boundaries. -/
theorem SourceLemma10_3Data.omittedFixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_3Data hp hp1 W) (hW : IsOpen W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), D m)ᶜ ×ˢ V) ∧
    ∀ q ∈ ((⋃ m : ℤ, ⋃ (_ : m ≠ n), D m)ᶜ ×ˢ V),
      sourceStandardRootOmittedJointProduct hp hp1 n q ≠ 0 := by
  have hsub : ((⋃ m : ℤ, ⋃ (_ : m ≠ n), D m)ᶜ ×ˢ V) ⊆
      sourceStandardRootOmittedJointDomain hp hp1 W n := by
    intro q hq
    refine ⟨hVW hq.2,?_⟩
    intro m hm hseg
    exact hq.1 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hm,hD.gap q.2 hq.2 m hseg⟩⟩)
  have hj := h.omittedJoint hW n
  exact ⟨hj.2.1.mono hsub,fun q hq => hj.2.2.2 q (hsub hq)⟩

/-- The whole omitted disk avoids every unomitted actual gap. -/
theorem SourceIsolatingNeighborhoods.disk_subset_omittedDomain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    D n ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  intro z hz m hm hseg
  exact Set.disjoint_left.mp (hD.disjoint n m hm.symm) hz (hD.gap ψ hψ m hseg)

/-- Omitting one root preserves locally uniform absolute paired tails beyond a finite cutoff. -/
theorem exists_uniform_absolute_sourceStandardRootOmittedPairedFactor_tails (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (R : ℝ) (hR : 0 ≤ R) (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ N₀ : ℕ, ∃ E : ℕ → ℝ,
      Tendsto E atTop (𝓝 0) ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ V, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : Finset ℕ,
        (∀ j ∈ s, N ≤ j) →
        (∑ j ∈ s, ‖sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j-1‖) ≤ E N := by
  obtain ⟨V,ho,hφ,N₀,E,hE,hbound⟩ :=
    exists_uniform_absolute_sourceStandardRootPairedFactor_tails hp hp1 φ R hR
  refine ⟨V,ho,hφ,max N₀ n.natAbs,E,hE,?_⟩
  intro N hN ψ hψ z hz s hs
  have he : (∑ j ∈ s, ‖sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j-1‖) =
      ∑ j ∈ s, ‖sourceStandardRootPairedFactor hp hp1 ψ z j-1‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sourceStandardRootOmittedPairedFactor_eq_of_ne hp hp1 ψ z n j
      (by have := hs j hj; have := (le_max_right N₀ n.natAbs).trans hN; omega)]
  rw [he]
  exact hbound N ((le_max_left _ _).trans hN) ψ hψ z hz s hs

/-- Literal symmetric cutoffs converge uniformly on every compact subset of the joint domain. -/
theorem SourceLemma10_3Data.omittedCompact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_3Data hp hp1 W) (hW : IsOpen W) (n : ℤ)
    (K : Set (ℂ × CoeffPair p)) (hK : IsCompact K)
    (hsub : K ⊆ sourceStandardRootOmittedJointDomain hp hp1 W n) :
    TendstoUniformlyOn (sourceStandardRootOmittedPartialProduct hp hp1 n)
      (sourceStandardRootOmittedJointProduct hp hp1 n) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((h.omittedJoint hW n).2.2.1.mono hsub)

/-- The literal closed-disk complement printed in Lemma 10.5. -/
theorem SourceLemma10_3Data.omittedClosedFixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_3Data hp hp1 W) (hW : IsOpen W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ V) ∧
    ∀ q ∈ ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ V),
      sourceStandardRootOmittedJointProduct hp hp1 n q ≠ 0 := by
  have hsub : ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ V) ⊆
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), D m)ᶜ ×ˢ V) := by
    intro q hq
    refine ⟨?_,hq.2⟩
    intro hmem
    obtain ⟨m,hm⟩ := mem_iUnion.mp hmem
    obtain ⟨hmn,hm⟩ := mem_iUnion.mp hm
    exact hq.1 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hmn,subset_closure hm⟩⟩)
  have hf := h.omittedFixed hW hVW hD n
  exact ⟨hf.1.mono hsub,fun q hq => hf.2 q (hsub hq)⟩

/-- At a fixed source, convergence is uniform on every spectral compact subset of the natural domain. -/
theorem SourceLemma10_3Data.omittedSpectralCompact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_3Data hp hp1 W) (hW : IsOpen W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    TendstoUniformlyOn (fun N z => sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ))
      (sourceStandardRootOmittedProduct hp hp1 n ψ) atTop K := by
  have hi : IsCompact ((fun z : ℂ => (z,ψ)) '' K) :=
    hK.image (continuous_id.prodMk continuous_const)
  have hc := h.omittedCompact hW n _ hi (by
    rintro q ⟨z,hz,rfl⟩
    exact ⟨hψ,hsub hz⟩)
  intro u hu
  filter_upwards [hc u hu] with N hN
  intro z hz
  exact hN (z,ψ) ⟨z,hz,rfl⟩

/-- The quantified omitted domain is the literal complement of the union of unomitted gaps. -/
theorem sourceStandardRootOmittedDomain_eq_compl_iUnion (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceStandardRootOmittedDomain hp hp1 ψ n =
      (⋃ m : ℤ, ⋃ (_ : m ≠ n), sourcePeriodicSegment hp hp1 ψ m)ᶜ := by
  ext z
  simp [sourceStandardRootOmittedDomain]

end NLS.ZakharovShabat
