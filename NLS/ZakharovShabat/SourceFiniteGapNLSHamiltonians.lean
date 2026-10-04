import NLS.ZakharovShabat.SourceFiniteGapSmoothRealization
import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # Physical NLS Hamiltonians of the original finite-gap source

The Appendix H hierarchy is evaluated on the actual smooth period-one
Fourier representative. Its first term agrees with the original source
mass pairing at every finite exponent.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Appendix H Hamiltonians of a finite-gap source, defined through
its original Fourier series and the physical differential recurrence. -/
def sourceFiniteGapNLSHamiltonian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) : ℂ :=
  classicalNLSHamiltonian (sourceFiniteGapPhysicalPair hp hp1 φ hf).1
    (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 k

/-- The physical hierarchy retains the calibrated source mass normalization. -/
theorem sourceFiniteGapNLSHamiltonian_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 = ∑' n : ℤ, φ.val.fst n*φ.val.snd (-n) := by
  rw [sourceFiniteGapNLSHamiltonian,classicalNLSHamiltonian_one,
    ← tsum_bilinear_unitFourierCoefficient
      (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).1.continuous
      (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).2.continuous]
  have h₁ (n : ℤ) : unitFourierCoefficient (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 n = φ.val.fst n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact (periodOneCoefficient_sourceFiniteGapPhysicalPair hp hp1 φ hf n).1
  have h₂ (n : ℤ) : unitFourierCoefficient (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 n = φ.val.snd n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact (periodOneCoefficient_sourceFiniteGapPhysicalPair hp hp1 φ hf n).2
  simp only [h₁,h₂]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => φ.val.fst n*φ.val.snd (-n))]
  simp only [Equiv.neg_apply,neg_neg]

end NLS.ZakharovShabat
