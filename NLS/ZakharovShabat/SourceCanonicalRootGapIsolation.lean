import NLS.ZakharovShabat.SourceCanonicalRootGapSides
import NLS.ZakharovShabat.SourceGlobalIsolation
import NLS.ZakharovShabat.SourceSymmetricContour

/-!
# Separation of gap points from all other gaps

The common isolating discs of Lemma 10.1 contain the straight periodic
segments and are pairwise disjoint. Thus each point of one gap belongs
to the open domain of its complementary omitted-root product.
-/

noncomputable section
open Set Topology Metric Complex Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every point parametrized by a signed coordinate in `[-1,1]`
belongs to its canonical periodic gap segment. -/
theorem sourceCanonicalRootGapPoint_mem_segment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourcePeriodicSegment hp hp1 ψ n := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  change sourceCanonicalRootGapPoint hp hp1 ψ n t ∈ segment ℝ a b
  refine ⟨(1-t)/2, (1+t)/2, by linarith, by linarith, by ring, ?_⟩
  dsimp [sourceCanonicalRootGapPoint, sourceStandardRootMidpoint,
    sourceStandardRootHalfGap, canonicalPeriodicMidpoint, canonicalPeriodicGap,
    a, b]
  simp only [Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- One connected almost-real source domain has pairwise disjoint
canonical periodic gap segments. -/
theorem exists_global_source_disjoint_periodicSegments
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ i j : ℤ, i ≠ j →
        Disjoint (sourcePeriodicSegment hp hp1 ψ i)
          (sourcePeriodicSegment hp hp1 ψ j) := by
  obtain ⟨W,hWopen,hWconn,hreal,hdata⟩ :=
    exists_global_source_isolating_neighborhood hp hp1
  refine ⟨W,hWopen,hWconn,hreal,?_⟩
  intro ψ hψ i j hij
  obtain ⟨V,_,_,hψV,_,φ,N,ε,_,_,_,hseg,hdisjoint⟩ := hdata ψ hψ
  exact (hdisjoint i j hij).mono (hseg ψ hψV i) (hseg ψ hψV j)

/-- On the same source domain, every point of the `n`th gap avoids all
other gap segments and so lies in the omitted-product domain. -/
theorem exists_global_source_gapPoint_mem_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ, ∀ t : ℝ,
        -1 ≤ t → t ≤ 1 →
        sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
          sourceStandardRootOmittedDomain hp hp1 ψ n := by
  obtain ⟨W,hWopen,hWconn,hreal,hdisjoint⟩ :=
    exists_global_source_disjoint_periodicSegments hp hp1
  refine ⟨W,hWopen,hWconn,hreal,?_⟩
  intro ψ hψ n t htl htr m hmn
  have hpoint := sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n t htl htr
  exact Set.disjoint_left.mp (hdisjoint ψ hψ n m (Ne.symm hmn)) hpoint

/-- All clauses of Lemma 10.7 hold on one connected almost-real source
domain: joint analyticity off the gaps, analytic extension through a
collapsed gap, and opposite one-sided values on a noncollapsed gap. -/
theorem exists_global_source_canonicalRoot_gapSide_theorem
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W) ∧
      (∀ ψ ∈ W, ∀ n : ℤ,
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n = 0 →
        AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 ψ)
          (sourceStandardRootOmittedDomain hp hp1 ψ n)) ∧
      ∀ ψ ∈ W, ∀ n : ℤ, ∀ t : ℝ,
        -1 ≤ t → t ≤ 1 →
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n ≠ 0 →
        Tendsto (sourceCanonicalRoot hp hp1 ψ)
          (𝓝[standardRootGapUpperSide
            (sourceStandardRootMidpoint hp hp1 ψ n)
            (sourceStandardRootHalfGap hp hp1 ψ n)]
              (sourceCanonicalRootGapPoint hp hp1 ψ n t))
          (𝓝 (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) ∧
        Tendsto (sourceCanonicalRoot hp hp1 ψ)
          (𝓝[standardRootGapLowerSide
            (sourceStandardRootMidpoint hp hp1 ψ n)
            (sourceStandardRootHalfGap hp hp1 ψ n)]
              (sourceCanonicalRootGapPoint hp hp1 ψ n t))
          (𝓝 (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) ∧
        sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
          -sourceCanonicalRootGapLowerValue hp hp1 ψ n t := by
  obtain ⟨W,hWopen,hWconn,hreal,hlocal⟩ :=
    exists_global_source_isolating_neighborhood hp hp1
  have hA : ∀ ψ ∈ W, ∀ n : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) n) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) n)^2) ψ := by
    intro ψ hψ n
    obtain ⟨V,hVopen,_,hψV,_,φ,N,ε,hε,_,hcluster,_,hdisjoint⟩ := hlocal ψ hψ
    exact analyticAt_canonicalPeriodicMidpoint_squaredGap_of_sourceIsolating
      hp hp1 φ ψ N ε hε V hVopen hψV hcluster hdisjoint n
  have hfull := sourceCanonicalRootJointProduct_analyticOnNhd_of_symmetric
    hp hp1 W hWopen hA
  have hprod (n : ℤ) : AnalyticOnNhd ℂ
      (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) :=
    (sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric
      hp hp1 W hWopen hA n).2
  have hdisjoint (ψ : CoeffPair p) (hψ : ψ ∈ W) (i j : ℤ) (hij : i ≠ j) :
      Disjoint (sourcePeriodicSegment hp hp1 ψ i)
        (sourcePeriodicSegment hp hp1 ψ j) := by
    obtain ⟨V,_,_,hψV,_,φ,N,ε,_,_,_,hseg,hdisc⟩ := hlocal ψ hψ
    exact (hdisc i j hij).mono (hseg ψ hψV i) (hseg ψ hψV j)
  refine ⟨W,hWopen,hWconn,hreal,hfull.1,hfull.2,?_,?_⟩
  · intro ψ hψ n hgap
    exact sourceCanonicalRoot_analyticOnNhd_of_zeroGap hp hp1 W n
      (hprod n) ψ hψ hgap
  · intro ψ hψ n t htl htr hgap
    have hpoint := sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n t htl htr
    have hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
        sourceStandardRootOmittedDomain hp hp1 ψ n := by
      intro m hmn
      exact Set.disjoint_left.mp (hdisjoint ψ hψ n m (Ne.symm hmn)) hpoint
    have hspectral := sourceStandardRootOmittedProduct_analyticOnNhd_spectral
      hp hp1 n W (hprod n) ψ hψ
    exact ⟨sourceCanonicalRoot_tendsto_gap_upper_side hp hp1 ψ n t
        hgap htl htr hother hspectral,
      sourceCanonicalRoot_tendsto_gap_lower_side hp hp1 ψ n t
        hgap htl htr hother hspectral,
      sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 ψ n t⟩

end NLS.ZakharovShabat
