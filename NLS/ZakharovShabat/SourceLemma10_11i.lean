import NLS.ZakharovShabat.SourceCriticalRootRatioOpenGapDomain

/-!
# Lemma 10.11(i) on the unchanged common source domain

One explicit normalized product extends the actual critical-root quotient
analytically to the plane with only the noncollapsed gap segments removed.
It agrees with each omitted extension through a collapsed gap, including
central and infinitely many collapsed gaps. The preceding common source
domain and its original isolating disks are retained. The path-integral
assertions in part (ii) are separate.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 10.11(i), with one actual extension and all preceding common-domain data. -/
structure SourceLemma10_11iData (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceEquation2_15Data hp hp1 W
  domain_open : ∀ ψ ∈ W, IsOpen (sourceOpenGapComplement hp hp1 ψ)
  analytic : ∀ ψ ∈ W,
    AnalyticOnNhd ℂ (sourceCriticalRootRatioContinued hp hp1 ψ) (sourceOpenGapComplement hp hp1 ψ)
  agreement : ∀ ψ ∈ W, ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
    sourceCriticalRootRatioContinued hp hp1 ψ z =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z
  collapsed : ∀ ψ ∈ W, ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
    ∀ z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n,
      sourceCriticalRootRatioContinued hp hp1 ψ z = sourceCriticalRootRatioExtension hp hp1 n ψ z

/-- Removing all collapsed gaps preserves the source domain of equation (2.15). -/
theorem SourceEquation2_15Data.collapsedContinuation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} (h : SourceEquation2_15Data hp hp1 W) :
    SourceLemma10_11iData hp hp1 W :=
  ⟨h,h.isOpen_openGapComplement,h.continued_analytic_openGapComplement,
    h.continued_eq_quotient,h.continued_eq_extension⟩

/-- The whole original selected disk is covered when its gap collapses, at complex sources too. -/
theorem SourceLemma10_11iData.continued_analytic_originalDisk
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11iData hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioContinued hp hp1 ψ) (D n) ∧
      ∀ z ∈ D n, sourceCriticalRootRatioContinued hp hp1 ψ z = sourceCriticalRootRatioExtension hp hp1 n ψ z :=
  ⟨(h.previous.continued_analytic_omittedDomain ψ (hVW hψ) n hg).mono
      (hD.disk_subset_omittedDomain ψ hψ n),
    fun z hz => h.collapsed ψ (hVW hψ) n hg z (hD.disk_subset_omittedDomain ψ hψ n hz)⟩

/-- The literal extension assertion on the complement of the union of all noncollapsed gaps. -/
theorem SourceLemma10_11iData.exists_analytic_extension
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} (h : SourceLemma10_11iData hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (⋃ m : ℤ, ⋃ (_ : canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0), sourcePeriodicSegment hp hp1 ψ m)ᶜ ∧
      ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
        F z = deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z := by
  refine ⟨sourceCriticalRootRatioContinued hp hp1 ψ,?_,h.agreement ψ hψ⟩
  rw [← sourceOpenGapComplement_eq_compl_iUnion]
  exact h.analytic ψ hψ

/-- Lemma 10.11(i) for every finite p>1 on the retained common almost-real source domain. -/
theorem sourceLemma10_11i (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_11iData hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceEquation2_15 hp hp1
  exact ⟨W,ho,hc,hr,h.collapsedContinuation⟩

end NLS.ZakharovShabat
