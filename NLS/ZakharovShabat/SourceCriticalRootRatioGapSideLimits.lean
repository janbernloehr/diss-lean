import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideRegularity
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# One-sided limits of the full critical-root quotient

At an interior point of a noncollapsed gap, the full canonical root
has nonzero and opposite upper and lower boundary values. Dividing
the continuous discriminant derivative by its one-sided root limits
gives the actual one-sided limits of the critical-root quotient.
-/

noncomputable section
open Set Complex Filter
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper canonical-root boundary value is nonzero at every
interior point of a noncollapsed selected gap. -/
theorem sourceCanonicalRootGapUpperValue_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (ht : t ∈ Ioo (-1) 1)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceCanonicalRootGapUpperValue hp hp1 ψ n t ≠ 0 := by
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 := by
    dsimp [δ, sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  have hrad : 0 < 1-t^2 := by
    have h₁ : 0 < 1+t := by linarith [ht.1]
    have h₂ : 0 < 1-t := by linarith [ht.2]
    nlinarith [mul_pos h₁ h₂]
  have hsqrt : (Real.sqrt (1-t^2):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hrad).ne'
  have hprod := sourceStandardRootOmittedProduct_ne_zero
    hp hp1 ψ (sourceCanonicalRootGapPoint hp hp1 ψ n t) n hother
  change 2*I * (-δ*I*(Real.sqrt (1-t^2):ℂ)) *
    sourceStandardRootOmittedProduct hp hp1 n ψ
      (sourceCanonicalRootGapPoint hp hp1 ψ n t) ≠ 0
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) I_ne_zero)
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδ) I_ne_zero) hsqrt))
    hprod

/-- The lower canonical-root boundary value is also nonzero. -/
theorem sourceCanonicalRootGapLowerValue_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (ht : t ∈ Ioo (-1) 1)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceCanonicalRootGapLowerValue hp hp1 ψ n t ≠ 0 := by
  have hupper := sourceCanonicalRootGapUpperValue_ne_zero
    hp hp1 ψ n t hgap ht hother
  rw [sourceCanonicalRootGapUpperValue_eq_neg_lower] at hupper
  exact fun h => hupper (by rw [h]; simp)

/-- The actual discriminant quotient tends to its upper boundary
quotient from anywhere in the open upper side of the gap. -/
theorem sourceCriticalRootRatio_tendsto_gap_upper_side
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (ht : t ∈ Ioo (-1) 1)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hprod : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n)) :
    Tendsto
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) := by
  have hnum : Tendsto
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))) :=
    ((analyticOnNhd_discriminant_derivative hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) _
      (mem_univ _)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hroot := sourceCanonicalRoot_tendsto_gap_upper_side
    hp hp1 ψ n t hgap ht.1.le ht.2.le hother hprod
  exact hnum.div hroot
    (sourceCanonicalRootGapUpperValue_ne_zero hp hp1 ψ n t hgap ht hother)

/-- The lower-side quotient limit has the opposite denominator. -/
theorem sourceCriticalRootRatio_tendsto_gap_lower_side
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (ht : t ∈ Ioo (-1) 1)
    (hother : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hprod : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n)) :
    Tendsto
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
        sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) := by
  have hnum : Tendsto
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
          (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))) :=
    ((analyticOnNhd_discriminant_derivative hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) _
      (mem_univ _)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hroot := sourceCanonicalRoot_tendsto_gap_lower_side
    hp hp1 ψ n t hgap ht.1.le ht.2.le hother hprod
  exact hnum.div hroot
    (sourceCanonicalRootGapLowerValue_ne_zero hp hp1 ψ n t hgap ht hother)

/-- Both one-sided quotient limits hold on an open neighborhood of the
real-type source locus, uniformly in the choice of gap index and
interior longitudinal parameter. -/
theorem exists_global_sourceCriticalRootRatio_gapSideLimits
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ, ∀ t : ℝ,
        t ∈ Ioo (-1) 1 →
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n ≠ 0 →
        Tendsto
          (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
            sourceCanonicalRoot hp hp1 ψ z)
          (𝓝[standardRootGapUpperSide
            (sourceStandardRootMidpoint hp hp1 ψ n)
            (sourceStandardRootHalfGap hp hp1 ψ n)]
              (sourceCanonicalRootGapPoint hp hp1 ψ n t))
          (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
            sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) ∧
        Tendsto
          (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
            sourceCanonicalRoot hp hp1 ψ z)
          (𝓝[standardRootGapLowerSide
            (sourceStandardRootMidpoint hp hp1 ψ n)
            (sourceStandardRootHalfGap hp hp1 ψ n)]
              (sourceCanonicalRootGapPoint hp hp1 ψ n t))
          (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
            sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) := by
  obtain ⟨W₁,hW₁open,_,hreal₁,_,_,_,hsides⟩ :=
    exists_global_source_canonicalRoot_gapSide_theorem hp hp1
  obtain ⟨W₂,hW₂open,_,hreal₂,hother⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  let W := W₁ ∩ W₂
  refine ⟨W,hW₁open.inter hW₂open,
    (fun ψ hψ => ⟨hreal₁ hψ,hreal₂ hψ⟩),?_⟩
  intro ψ hψ n t ht hgap
  have hdom := hother ψ hψ.2 n t ht.1.le ht.2.le
  have hnum : Tendsto
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (𝓝 (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))) :=
    (analyticOnNhd_discriminant_derivative hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) _
      (mem_univ _)).continuousAt.tendsto
  have hs := hsides ψ hψ.1 n t ht.1.le ht.2.le hgap
  constructor
  · exact (hnum.mono_left nhdsWithin_le_nhds).div hs.1
      (sourceCanonicalRootGapUpperValue_ne_zero hp hp1 ψ n t hgap ht hdom)
  · exact (hnum.mono_left nhdsWithin_le_nhds).div hs.2.1
      (sourceCanonicalRootGapLowerValue_ne_zero hp hp1 ψ n t hgap ht hdom)

end NLS.ZakharovShabat
