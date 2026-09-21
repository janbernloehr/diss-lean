import NLS.ZakharovShabat.CanonicalPeriodicContinuity

/-!
# Real paths from the free potential

Real scaling preserves real type and even Fourier support. The canonical
periodic coordinates are continuous along the resulting path through every
real parameter, including spectral collisions.
-/

noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Multiplication by a real scalar preserves the Fourier real-type relation. -/
theorem IsRealType.ofReal_smul {φ : PairSpace p} (hφ : IsRealType φ) (t : ℝ) :
    IsRealType ((t : ℂ) • φ) := by
  intro n
  change (t : ℂ)*(φ.2 n) = conj ((t : ℂ)*(φ.1 (-n)))
  rw [map_mul, Complex.conj_ofReal, hφ n]

/-- The even-potential path obtained by real scaling. -/
def realPotentialPath (φ : pairParitySubspace (p := p) 0) (t : ℝ) : pairParitySubspace (p := p) 0 :=
  (t : ℂ) • φ

@[simp] theorem realPotentialPath_zero (φ : pairParitySubspace (p := p) 0) :
    realPotentialPath φ 0 = 0 := by simp [realPotentialPath]

@[simp] theorem realPotentialPath_one (φ : pairParitySubspace (p := p) 0) :
    realPotentialPath φ 1 = φ := by simp [realPotentialPath]

/-- The real scaling path is continuous in the even potential space. -/
theorem continuous_realPotentialPath (φ : pairParitySubspace (p := p) 0) :
    Continuous (realPotentialPath φ) := continuous_ofReal.smul continuous_const

/-- Every point of the scaling path is real type when its endpoint is real type. -/
theorem realPotentialPath_isRealType (φ : pairParitySubspace (p := p) 0)
    (hφ : IsRealType φ.val) (t : ℝ) : IsRealType (realPotentialPath φ t).val := hφ.ofReal_smul t

/-- Each canonical periodic endpoint slot varies continuously along real scaling. -/
theorem continuous_canonicalPeriodicSlot_realPotentialPath (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hφ : IsRealType φ.val) (k : ℤ ×ₗ Fin 2) :
    Continuous (fun t : ℝ => canonicalPeriodicSlot hp hp1 (realPotentialPath φ t).val
      (realPotentialPath φ t).property k) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (continuousAt_canonicalPeriodicSlot_of_realType hp hp1 (realPotentialPath φ t)
    (realPotentialPath_isRealType φ hφ t) k).comp (continuous_realPotentialPath φ).continuousAt

end NLS.ZakharovShabat
