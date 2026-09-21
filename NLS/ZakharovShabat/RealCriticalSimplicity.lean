import NLS.ZakharovShabat.CanonicalCriticalInterlacing

/-!
# Simplicity of every critical point at real-type potentials

The strictly increasing canonical critical sequence has exactly one
occurrence of each value. Its exact global multiplicity formula therefore
makes every critical zero simple, including those in the central cluster.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every canonical real-type critical point has natural analytic multiplicity one. -/
theorem analyticOrderNatAt_canonicalCriticalPoints_eq_one_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) :
    analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) (canonicalCriticalPoints hp hp1 φ heven n) = 1 := by
  rw [← canonicalCriticalPoints_multiplicity hp hp1 φ heven]
  rw [finsum_eq_single _ n]
  · simp
  · intro m hmn
    have he : canonicalCriticalPoints hp hp1 φ heven m ≠ canonicalCriticalPoints hp hp1 φ heven n :=
      fun h => hmn ((canonicalCriticalPoints_injective_of_realType hp hp1 φ heven hreal) h)
    simp only [if_neg he]

/-- Every canonical real-type critical point is a simple analytic zero of the derivative. -/
theorem analyticOrderAt_canonicalCriticalPoints_eq_one_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) :
    analyticOrderAt (deriv (canonicalDiscriminant hp φ)) (canonicalCriticalPoints hp hp1 φ heven n) = 1 := by
  have h := analyticOrderNatAt_canonicalCriticalPoints_eq_one_of_realType hp hp1 φ heven hreal n
  exact (ENat.toNat_eq_iff_eq_natCast _ 1).mp h

/-- All discriminant critical points are simple at real-type potentials, with no cutoff restriction. -/
theorem analyticOrderAt_discriminant_critical_eq_one_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (z : ℂ) (hz : deriv (canonicalDiscriminant hp φ) z = 0) :
    analyticOrderAt (deriv (canonicalDiscriminant hp φ)) z = 1 := by
  obtain ⟨n,rfl⟩ := (canonicalCriticalPoints_exhaustive hp hp1 φ heven z).mp hz
  exact analyticOrderAt_canonicalCriticalPoints_eq_one_of_realType hp hp1 φ heven hreal n

/-- The second spectral derivative never vanishes at a real-type discriminant critical point. -/
theorem discriminant_second_derivative_ne_zero_at_critical_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (z : ℂ) (hz : deriv (canonicalDiscriminant hp φ) z = 0) :
    deriv (deriv (canonicalDiscriminant hp φ)) z ≠ 0 := by
  have ha := analyticOnNhd_discriminant_derivative hp hp1 φ heven z (mem_univ _)
  have ho := analyticOrderAt_discriminant_critical_eq_one_of_realType hp hp1 φ heven hreal z hz
  have hd : analyticOrderAt (deriv (deriv (canonicalDiscriminant hp φ))) z = 0 :=
    analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa using ho)
  intro hzero
  exact (ha.deriv.analyticOrderAt_ne_zero.mpr hzero) hd

end NLS.ZakharovShabat
