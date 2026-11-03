import NLS.ZakharovShabat.EvenDiscriminantPeriodicEndpoints
import NLS.ZakharovShabat.RealCriticalSimplicity
import NLS.ComplexAnalysis.EvenSpectralDerivatives

/-! # Complete critical reflection for an even real-type discriminant

Actual gap interlacing and uniqueness identify the reflected canonical
critical coordinate, including the central and collapsed gaps. Strict
order then makes every positive-index critical point strictly positive.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
  (hφ : φ ∈ pairParitySubspace 0) (hr : IsRealType φ)
  (he : ∀ z, canonicalDiscriminant hp φ (-z) = canonicalDiscriminant hp φ z)
include hr he

theorem canonicalCriticalPoints_neg_of_discriminant_even_of_realType (n : ℤ) :
    canonicalCriticalPoints hp hp1 φ hφ (-n) = -canonicalCriticalPoints hp hp1 φ hφ n := by
  apply (critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ hφ hr (-n)
    (-canonicalCriticalPoints hp hp1 φ hφ n) ?_ ?_).symm
  · rw [deriv_neg_argument_of_even _ he,canonicalCriticalPoints_is_critical,neg_zero]
  · obtain ⟨hl,hu⟩ := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 φ hφ hr n
    obtain ⟨hleft,hright⟩ := canonicalPeriodicEndpoints_neg_of_discriminant_even hp hp1 φ hφ he n
    rw [hleft,hright]
    simp only [neg_re,mem_Icc]
    exact ⟨neg_le_neg hu,neg_le_neg hl⟩

theorem canonicalCriticalPoints_zero_of_discriminant_even_of_realType :
    canonicalCriticalPoints hp hp1 φ hφ 0 = 0 := by
  have h := canonicalCriticalPoints_neg_of_discriminant_even_of_realType hp hp1 φ hφ hr he 0
  simp only [neg_zero] at h
  linear_combination h / 2

theorem canonicalCriticalPoints_re_pos_of_discriminant_even_of_realType
    (n : ℤ) (hn : 0 < n) : 0 < (canonicalCriticalPoints hp hp1 φ hφ n).re := by
  have h := strictMono_canonicalCriticalPoints_re_of_realType hp hp1 φ hφ hr hn
  dsimp only at h
  rwa [canonicalCriticalPoints_zero_of_discriminant_even_of_realType hp hp1 φ hφ hr he,zero_re] at h

end NLS.ZakharovShabat
