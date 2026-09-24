import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform
import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic
import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-!
# The collapsed-gap extension in Lemma 10.11

At a collapsed gap, the indexed critical point equals the periodic
midpoint. Its factor in the derivative product therefore cancels the
linear standard-root factor. The deleted quotient of Corollary 10.6
provides an analytic continuation across that gap.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The analytic candidate for the discriminant derivative divided by
the canonical root after deleting one common spectral factor. -/
def sourceCriticalRootRatioExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  -I * sourceSingleRootQuotientJointProduct hp hp1 n
    (z,(canonicalCriticalDisplacement hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))

/-- On an open almost-real source domain, a collapsed gap is removable
for the critical derivative divided by the canonical root. -/
theorem exists_global_sourceCriticalRootRatio_analytic_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
          AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
            (sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
          ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
            sourceCriticalRootRatioExtension hp hp1 n ψ z =
              deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
                sourceCanonicalRoot hp hp1 ψ z := by
  obtain ⟨W₁,hW₁open,_,hreal₁,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  obtain ⟨W₂,hW₂open,_,hreal₂,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  let W := W₁ ∩ W₂
  refine ⟨W,hW₁open.inter hW₂open,
    fun ψ hψ => ⟨hreal₁ hψ,hreal₂ hψ⟩,?_⟩
  intro ψ hψ n hgap
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hcrit : canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    have h := (hexact ψ hψ.2 n).2
    rw [hgap] at h
    exact sub_eq_zero.mp (by simpa using h)
  have ha : displacedRoots a n =
      canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    simp only [a, displacedRoots, canonicalCriticalDisplacement_apply]
    linear_combination hcrit
  constructor
  · intro z hz
    have hQ : AnalyticAt ℂ
        (sourceSingleRootQuotientJointProduct hp hp1 n)
        (z,(a,ψ)) :=
      (hdata n).2 (z,(a,ψ)) ⟨hψ.1,hz⟩
    have hmap : AnalyticAt ℂ (fun w : ℂ => (w,(a,ψ))) z :=
      analyticAt_id.prod (analyticAt_const.prod analyticAt_const)
    change AnalyticAt ℂ (fun w =>
      -I * sourceSingleRootQuotientJointProduct hp hp1 n (w,(a,ψ))) z
    exact analyticAt_const.mul (hQ.comp (f := fun w : ℂ => (w,(a,ψ))) hmap)
  · intro z hz
    have hzn : z ∉ sourcePeriodicSegment hp hp1 ψ n := hz n
    have hlinear : canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z ≠ 0 := by
      rw [← sourceStandardRoot_of_zeroGap hp hp1 ψ n z
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)]
      exact sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hzn
    have homit : sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0 :=
      sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n
        (fun m _ => hz m)
    have hderiv := discriminant_derivative_eq_canonicalCriticalProduct hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z
    have hseq : displacedRoots a = canonicalCriticalPoints hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) := by
      funext m
      simp only [a, displacedRoots, canonicalCriticalDisplacement_apply]
      ring
    rw [← hseq] at hderiv
    have hfactor := jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)
    have hroot := sourceCanonicalRoot_eq_omitted hp hp1 n ψ z
    rw [hderiv]
    change sourceCriticalRootRatioExtension hp hp1 n ψ z =
      jointSingleSpectralProduct (z,a) / sourceCanonicalRoot hp hp1 ψ z
    rw [hfactor,hroot]
    rw [show displacedRoots a n-z =
        canonicalPeriodicMidpoint hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z
      from congrArg (· - z) ha]
    rw [sourceStandardRoot_of_zeroGap hp hp1 ψ n z
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)]
    change -I * (jointDeletedSingleSpectralProduct n (z,a) /
      sourceStandardRootOmittedProduct hp hp1 n ψ z) =
      2 * _ * jointDeletedSingleSpectralProduct n (z,a) /
        (2*I * _ * sourceStandardRootOmittedProduct hp hp1 n ψ z)
    field_simp [hlinear,homit]
    simp

end NLS.ZakharovShabat
