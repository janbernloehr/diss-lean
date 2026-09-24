import NLS.ZakharovShabat.SourceCriticalRootRatioFactorization
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import NLS.ZakharovShabat.RealGapCanonicalRootLowerIntegral

/-!
# Gap-side boundary values of the critical-root quotient

At an interior point of a noncollapsed periodic gap, the actual
discriminant derivative divided by the full canonical-root boundary
value equals the selected critical factor times the analytic deleted
quotient, divided by the selected standard-root boundary value.
This is the pointwise bridge to the straight side-path integrals of
Lemma 10.4.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper-side quotient is the regular deleted factor over the
selected standard-root upper boundary value. -/
theorem discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (ht : t ∈ Ioo (-1) 1)
    (hdom : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
      sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n -
        sourceCanonicalRootGapPoint hp hp1 ψ n t) *
          sourceCriticalRootRatioExtension hp hp1 n ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n t)) /
        (-sourceStandardRootHalfGap hp hp1 ψ n * I *
          (Real.sqrt (1-t^2):ℂ)) := by
  let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let q := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let Q := jointDeletedSingleSpectralProduct n (z,a)
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ z
  let S := -δ*I*(Real.sqrt (1-t^2):ℂ)
  have hδ : δ ≠ 0 := by
    dsimp [δ,sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  have hrad : 0 < 1-t^2 := by
    have h₁ : 0 < 1+t := by linarith [ht.1]
    have h₂ : 0 < 1-t := by linarith [ht.2]
    nlinarith [mul_pos h₁ h₂]
  have hsqrt : (Real.sqrt (1-t^2):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hrad).ne'
  have hS : S ≠ 0 := by
    dsimp [S]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδ) I_ne_zero) hsqrt
  have hP : P ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hdom
  have hseq : displacedRoots a = canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) := by
    funext m
    simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
    ring
  have hderiv := discriminant_derivative_eq_canonicalCriticalProduct
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) z
  rw [← hseq] at hderiv
  have hfactor := jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)
  have hq : displacedRoots a n = q := by
    rw [hseq]
  have hD : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z =
      2*(q-z)*Q := by
    rw [hderiv]
    change jointSingleSpectralProduct (z,a) = _
    rw [hfactor,hq]
  change deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
    ((q-z)*sourceCriticalRootRatioExtension hp hp1 n ψ z)/S
  rw [hD]
  change (2*(q-z)*Q)/(2*I*S*P) = ((q-z)*(-I*(Q/P)))/S
  field_simp [hS,hP]
  simp [Complex.I_sq]

/-- The lower-side quotient has the opposite selected standard-root
boundary value in the denominator. -/
theorem discriminant_derivative_div_canonicalRootGapLowerValue_eq_selectedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (ht : t ∈ Ioo (-1) 1)
    (hdom : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
      sourceCanonicalRootGapLowerValue hp hp1 ψ n t =
      ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n -
        sourceCanonicalRootGapPoint hp hp1 ψ n t) *
          sourceCriticalRootRatioExtension hp hp1 n ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n t)) /
        (sourceStandardRootHalfGap hp hp1 ψ n * I *
          (Real.sqrt (1-t^2):ℂ)) := by
  have h := discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
    hp hp1 ψ n t hgap ht hdom
  rw [sourceCanonicalRootGapUpperValue_eq_neg_lower,div_neg] at h
  have hden : -sourceStandardRootHalfGap hp hp1 ψ n * I *
      (Real.sqrt (1-t^2):ℂ) =
        -(sourceStandardRootHalfGap hp hp1 ψ n * I *
          (Real.sqrt (1-t^2):ℂ)) := by ring
  rw [hden,div_neg] at h
  exact neg_inj.mp h

end NLS.ZakharovShabat
