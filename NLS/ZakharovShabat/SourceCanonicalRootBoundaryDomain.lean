import NLS.ZakharovShabat.SourceCanonicalRootCommonDomain
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import NLS.ZakharovShabat.SourceCanonicalRootGapSideSquare

/-!
# Closed-gap boundary data on the common source domain

The actual arbitrary-side limits are continuous through both gap endpoints.
They square to the source discriminant radicand, vanish at the endpoints,
and are opposite and nonzero in the interior of a noncollapsed gap.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A selected gap lies in the omitted domain on the same W, including both endpoints. -/
theorem SourceLemma10_5Data.canonicalGapPoint_mem
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := h.neighborhoods ψ hψ
  exact hD.toSourceIsolatingNeighborhoods.disk_subset_omittedDomain ψ hψV n
    (hD.gap ψ hψV n (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n t ht.1 ht.2))

/-- Boundary values vary continuously on the CLOSED gap for every source on W, not just real sources. -/
theorem SourceLemma10_5Data.canonicalBoundary_continuous
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    ContinuousOn (sourceCanonicalRootGapUpperValue hp hp1 ψ n) (Icc (-1:ℝ) 1) ∧
    ContinuousOn (sourceCanonicalRootGapLowerValue hp hp1 ψ n) (Icc (-1:ℝ) 1) := by
  have hpath : Continuous (sourceCanonicalRootGapPoint hp hp1 ψ n) := by
    unfold sourceCanonicalRootGapPoint
    fun_prop
  have hP : ContinuousOn (fun t : ℝ => sourceStandardRootOmittedProduct hp hp1 n ψ
      (sourceCanonicalRootGapPoint hp hp1 ψ n t)) (Icc (-1:ℝ) 1) :=
    (h.spectral ψ hψ n).continuousOn.comp hpath.continuousOn
      (fun t ht => h.canonicalGapPoint_mem ψ hψ n t ht)
  have hupper : Continuous (fun t : ℝ => 2*Complex.I *
      (-sourceStandardRootHalfGap hp hp1 ψ n*Complex.I*(Real.sqrt (1-t^2):ℂ))) := by fun_prop
  have hlower : Continuous (fun t : ℝ => 2*Complex.I *
      (sourceStandardRootHalfGap hp hp1 ψ n*Complex.I*(Real.sqrt (1-t^2):ℂ))) := by fun_prop
  exact ⟨hupper.continuousOn.mul hP,hlower.continuousOn.mul hP⟩

/-- Closed-gap endpoint boundary values vanish exactly. -/
theorem sourceCanonicalRootBoundary_endpoints (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourceCanonicalRootGapUpperValue hp hp1 ψ n (-1) = 0 ∧
    sourceCanonicalRootGapLowerValue hp hp1 ψ n (-1) = 0 ∧
    sourceCanonicalRootGapUpperValue hp hp1 ψ n 1 = 0 ∧
    sourceCanonicalRootGapLowerValue hp hp1 ψ n 1 = 0 := by
  simp [sourceCanonicalRootGapUpperValue,sourceCanonicalRootGapLowerValue]

/-- On a noncollapsed gap the two boundary traces are nonzero throughout the interior. -/
theorem SourceLemma10_5Data.canonicalBoundary_nonzero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    sourceCanonicalRootGapUpperValue hp hp1 ψ n t ≠ 0 ∧
    sourceCanonicalRootGapLowerValue hp hp1 ψ n t ≠ 0 := by
  have hd : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := div_ne_zero hg (by norm_num)
  have hs : (Real.sqrt (1-t^2):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by nlinarith [ht.1,ht.2])).ne'
  have hP := h.nonzero ψ n _ (h.canonicalGapPoint_mem ψ hψ n t ⟨ht.1.le,ht.2.le⟩)
  constructor
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hd) Complex.I_ne_zero) hs)) hP
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (mul_ne_zero (mul_ne_zero hd Complex.I_ne_zero) hs)) hP

/-- The post-lemma equation (2.14) uses the same W and includes endpoint approaches. -/
theorem SourceLemma10_5Data.canonicalBoundaryLimits
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    Tendsto (sourceCanonicalRoot hp hp1 ψ)
      (𝓝[standardRootGapUpperSide (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)] (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) ∧
    Tendsto (sourceCanonicalRoot hp hp1 ψ)
      (𝓝[standardRootGapLowerSide (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)] (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) ∧
    sourceCanonicalRootGapUpperValue hp hp1 ψ n t = -sourceCanonicalRootGapLowerValue hp hp1 ψ n t := by
  have hpoint := h.canonicalGapPoint_mem ψ hψ n t ht
  exact ⟨sourceCanonicalRoot_tendsto_gap_upper_side hp hp1 ψ n t hg ht.1 ht.2 hpoint (h.spectral ψ hψ n),
    sourceCanonicalRoot_tendsto_gap_lower_side hp hp1 ψ n t hg ht.1 ht.2 hpoint (h.spectral ψ hψ n),
    sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 ψ n t⟩


/-- Boundary data include actual side limits, continuity, endpoint values and the discriminant square. -/
structure SourceCanonicalRootBoundaryData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : Prop where
  upper_continuous : ContinuousOn (sourceCanonicalRootGapUpperValue hp hp1 ψ n) (Icc (-1:ℝ) 1)
  lower_continuous : ContinuousOn (sourceCanonicalRootGapLowerValue hp hp1 ψ n) (Icc (-1:ℝ) 1)
  opposite : ∀ t : ℝ, sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
    -sourceCanonicalRootGapLowerValue hp hp1 ψ n t
  upper_limit : ∀ t ∈ Icc (-1:ℝ) 1,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
    Tendsto (sourceCanonicalRoot hp hp1 ψ)
      (𝓝[standardRootGapUpperSide (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)] (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapUpperValue hp hp1 ψ n t))
  lower_limit : ∀ t ∈ Icc (-1:ℝ) 1,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
    Tendsto (sourceCanonicalRoot hp hp1 ψ)
      (𝓝[standardRootGapLowerSide (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)] (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapLowerValue hp hp1 ψ n t))
  endpoints : sourceCanonicalRootGapUpperValue hp hp1 ψ n (-1) = 0 ∧
    sourceCanonicalRootGapLowerValue hp hp1 ψ n (-1) = 0 ∧
    sourceCanonicalRootGapUpperValue hp hp1 ψ n 1 = 0 ∧
    sourceCanonicalRootGapLowerValue hp hp1 ψ n 1 = 0
  interior : ∀ t ∈ Ioo (-1:ℝ) 1,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
    sourceCanonicalRootGapUpperValue hp hp1 ψ n t ≠ 0 ∧
    sourceCanonicalRootGapLowerValue hp hp1 ψ n t ≠ 0
  upper_square : ∀ t ∈ Icc (-1:ℝ) 1,
    (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)^2 =
      (canonicalDiscriminant hp (periodOnePotential ψ) (sourceCanonicalRootGapPoint hp hp1 ψ n t))^2-4
  lower_square : ∀ t ∈ Icc (-1:ℝ) 1,
    (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)^2 =
      (canonicalDiscriminant hp (periodOnePotential ψ) (sourceCanonicalRootGapPoint hp hp1 ψ n t))^2-4

theorem SourceLemma10_5Data.canonicalBoundaryData
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    SourceCanonicalRootBoundaryData hp hp1 ψ n := by
  have hc := h.canonicalBoundary_continuous ψ hψ n
  refine ⟨hc.1,hc.2,sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 ψ n,
    fun t ht hg => (h.canonicalBoundaryLimits ψ hψ n t ht hg).1,
    fun t ht hg => (h.canonicalBoundaryLimits ψ hψ n t ht hg).2.1,
    sourceCanonicalRootBoundary_endpoints hp hp1 ψ n,
    h.canonicalBoundary_nonzero ψ hψ n,?_,?_⟩
  · intro t ht
    exact sourceCanonicalRootGapUpperValue_sq_eq_discriminant_sq_sub_four hp hp1 ψ n t ht.1 ht.2
      (h.canonicalGapPoint_mem ψ hψ n t ht)
  · intro t ht
    exact sourceCanonicalRootGapLowerValue_sq_eq_discriminant_sq_sub_four hp hp1 ψ n t ht.1 ht.2
      (h.canonicalGapPoint_mem ψ hψ n t ht)

end NLS.ZakharovShabat
