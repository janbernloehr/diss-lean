import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic
import NLS.ZakharovShabat.SourceStandardRootGapSideSourceJoint

/-!
# Gap-side values of the full canonical root

The complementary omitted product is analytic across the selected gap.
Multiplying its continuous boundary value by the two opposite side
values of the selected standard root proves equation (2.14).
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral point with signed longitudinal gap coordinate `t`. -/
def sourceCanonicalRootGapPoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ) : ℂ :=
  sourceStandardRootMidpoint hp hp1 ψ n +
    sourceStandardRootHalfGap hp hp1 ψ n * (t:ℂ)

/-- The upper-side canonical-root value at a gap point. -/
def sourceCanonicalRootGapUpperValue (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ) : ℂ :=
  2*I * (-sourceStandardRootHalfGap hp hp1 ψ n * I *
    (Real.sqrt (1-t^2):ℂ)) *
    sourceStandardRootOmittedProduct hp hp1 n ψ
      (sourceCanonicalRootGapPoint hp hp1 ψ n t)

/-- The lower-side canonical-root value at a gap point. -/
def sourceCanonicalRootGapLowerValue (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ) : ℂ :=
  2*I * (sourceStandardRootHalfGap hp hp1 ψ n * I *
    (Real.sqrt (1-t^2):ℂ)) *
    sourceStandardRootOmittedProduct hp hp1 n ψ
      (sourceCanonicalRootGapPoint hp hp1 ψ n t)

/-- The two boundary values in equation (2.14) are exact negatives. -/
theorem sourceCanonicalRootGapUpperValue_eq_neg_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ) :
    sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
      -sourceCanonicalRootGapLowerValue hp hp1 ψ n t := by
  unfold sourceCanonicalRootGapUpperValue sourceCanonicalRootGapLowerValue
  ring

/-- The full canonical root approaches its upper boundary value from
anywhere in the open upper side of the selected noncollapsed gap. -/
theorem sourceCanonicalRoot_tendsto_gap_upper_side
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (htl : -1 ≤ t) (htr : t ≤ 1)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hprod : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n)) :
    Tendsto (sourceCanonicalRoot hp hp1 ψ)
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) := by
  have hroot := sourceStandardRoot_tendsto_gap_upper_side hp hp1 ψ n t hgap htl htr
  have hcont := (hprod (sourceCanonicalRootGapPoint hp hp1 ψ n t) hother).continuousAt
  have hpaired : Tendsto (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceStandardRootOmittedProduct hp hp1 n ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun _ : ℂ => (2*I : ℂ))
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (2*I : ℂ)) := tendsto_const_nhds
  have h : Tendsto (fun z => 2*I * sourceStandardRoot hp hp1 ψ n z *
      sourceStandardRootOmittedProduct hp hp1 n ψ z)
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) := by
    simpa only [sourceCanonicalRootGapUpperValue] using (hc.mul hroot).mul hpaired
  have heq : (fun z => 2*I * sourceStandardRoot hp hp1 ψ n z *
      sourceStandardRootOmittedProduct hp hp1 n ψ z) =
      sourceCanonicalRoot hp hp1 ψ := by
    funext z
    exact (sourceCanonicalRoot_eq_omitted hp hp1 n ψ z).symm
  rw [heq] at h
  exact h

/-- The full canonical root approaches its lower boundary value from
anywhere in the open lower side of the selected noncollapsed gap. -/
theorem sourceCanonicalRoot_tendsto_gap_lower_side
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (htl : -1 ≤ t) (htr : t ≤ 1)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hprod : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n)) :
    Tendsto (sourceCanonicalRoot hp hp1 ψ)
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) := by
  have hroot := sourceStandardRoot_tendsto_gap_lower_side hp hp1 ψ n t hgap htl htr
  have hcont := (hprod (sourceCanonicalRootGapPoint hp hp1 ψ n t) hother).continuousAt
  have hpaired : Tendsto (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceStandardRootOmittedProduct hp hp1 n ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun _ : ℂ => (2*I : ℂ))
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (2*I : ℂ)) := tendsto_const_nhds
  have h : Tendsto (fun z => 2*I * sourceStandardRoot hp hp1 ψ n z *
      sourceStandardRootOmittedProduct hp hp1 n ψ z)
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) := by
    simpa only [sourceCanonicalRootGapLowerValue] using (hc.mul hroot).mul hpaired
  have heq : (fun z => 2*I * sourceStandardRoot hp hp1 ψ n z *
      sourceStandardRootOmittedProduct hp hp1 n ψ z) =
      sourceCanonicalRoot hp hp1 ψ := by
    funext z
    exact (sourceCanonicalRoot_eq_omitted hp hp1 n ψ z).symm
  rw [heq] at h
  exact h

end NLS.ZakharovShabat
