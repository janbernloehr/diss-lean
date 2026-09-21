import NLS.ZakharovShabat.RealCriticalSimplicity
import NLS.ComplexAnalysis.RealAxisSecondDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Strict real extrema of the discriminant

Every critical point at a real-type even potential is nondegenerate.
The real second-derivative test gives a strict local extremum, including
at collapsed gaps. Fermat's theorem and global interlacing show there is
exactly one real local extremum in each gap and no others.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Vanishing of the real-axis derivative is equivalent to vanishing of the full complex derivative. -/
theorem real_discriminant_deriv_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    deriv (fun y : ℝ => (canonicalDiscriminant hp φ y).re) x = 0 ↔
      deriv (canonicalDiscriminant hp φ) (x : ℂ) = 0 := by
  rw [deriv_real_axis_re _ (fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven z (mem_univ _)).differentiableAt)]
  constructor
  · intro hre
    exact Complex.ext hre (discriminant_derivative_im_eq_zero_of_realType hp hp1 φ heven hreal x)
  · intro hzero
    rw [hzero,zero_re]

/-- Every real discriminant critical point is a strict local minimum or maximum. -/
theorem discriminant_critical_strict_local_extremum (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ)
    (hz : deriv (canonicalDiscriminant hp φ) (x : ℂ) = 0) :
    (∀ᶠ y : ℝ in 𝓝[≠] x, (canonicalDiscriminant hp φ x).re < (canonicalDiscriminant hp φ y).re) ∨
      (∀ᶠ y : ℝ in 𝓝[≠] x, (canonicalDiscriminant hp φ y).re < (canonicalDiscriminant hp φ x).re) :=
  strict_local_extremum_of_complex_critical _
    (fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven z (mem_univ _)).differentiableAt)
    (fun z => (analyticOnNhd_discriminant_derivative hp hp1 φ heven z (mem_univ _)).differentiableAt)
    (canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ heven hreal) x hz
    (discriminant_second_derivative_ne_zero_at_critical_of_realType hp hp1 φ heven hreal x hz)

/-- Each indexed canonical critical coordinate is a strict local extremum on the real axis. -/
theorem canonicalCriticalPoints_strict_local_extremum (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    let c := (canonicalCriticalPoints hp hp1 φ heven n).re
    (∀ᶠ y : ℝ in 𝓝[≠] c, (canonicalDiscriminant hp φ c).re < (canonicalDiscriminant hp φ y).re) ∨
      (∀ᶠ y : ℝ in 𝓝[≠] c, (canonicalDiscriminant hp φ y).re < (canonicalDiscriminant hp φ c).re) := by
  have him := canonicalCriticalPoints_im_eq_zero hp hp1 φ heven hreal n
  have hc : ((canonicalCriticalPoints hp hp1 φ heven n).re : ℂ) = canonicalCriticalPoints hp hp1 φ heven n := by
    apply Complex.ext <;> simp [him]
  apply discriminant_critical_strict_local_extremum hp hp1 φ heven hreal
  rw [hc]
  exact canonicalCriticalPoints_is_critical hp hp1 φ heven n

/-- The real local extrema of the discriminant are exactly its critical points. -/
theorem isLocalExtr_real_discriminant_iff_critical (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    IsLocalExtr (fun y : ℝ => (canonicalDiscriminant hp φ y).re) x ↔
      deriv (canonicalDiscriminant hp φ) (x : ℂ) = 0 := by
  constructor
  · intro hx
    exact (real_discriminant_deriv_eq_zero_iff hp hp1 φ heven hreal x).mp hx.deriv_eq_zero
  · intro hx
    exact isLocalExtr_of_strict_punctured (discriminant_critical_strict_local_extremum hp hp1 φ heven hreal x hx)

/-- The canonical critical coordinates exhaust all real local extrema, with no additional extrema. -/
theorem isLocalExtr_real_discriminant_iff_canonical (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    IsLocalExtr (fun y : ℝ => (canonicalDiscriminant hp φ y).re) x ↔
      ∃ n : ℤ, canonicalCriticalPoints hp hp1 φ heven n = (x : ℂ) :=
  (isLocalExtr_real_discriminant_iff_critical hp hp1 φ heven hreal x).trans
    (canonicalCriticalPoints_exhaustive hp hp1 φ heven x)

/-- Every indexed real gap contains exactly one real local extremum, including collapsed gaps. -/
theorem existsUnique_localExtremum_in_canonicalPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    ∃! x : ℝ, IsLocalExtr (fun y : ℝ => (canonicalDiscriminant hp φ y).re) x ∧
      x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  refine ⟨(canonicalCriticalPoints hp hp1 φ heven n).re,
    ⟨isLocalExtr_of_strict_punctured (canonicalCriticalPoints_strict_local_extremum hp hp1 φ heven hreal n),
      canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 φ heven hreal n⟩,?_⟩
  intro x hx
  have hz := (isLocalExtr_real_discriminant_iff_critical hp hp1 φ heven hreal x).mp hx.1
  have he := critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ heven hreal n (x : ℂ) hz hx.2
  exact congrArg re he

end NLS.ZakharovShabat
