import NLS.ZakharovShabat.ClassicalNLSVectorField
import NLS.ZakharovShabat.SourceFiniteGapNLSHamiltonians

/-! # Physical NLS variations at the original finite-gap sources

The existing coefficient-preserving smooth representatives have the
correct conjugate-pair reality. Their actual third Hamiltonian has the
classical energy gradients, and its physical vector field is smooth,
periodic, and real. This identifies the physical field; equality with the
time derivative of the constructed spectral flow is a separate step.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ENNReal ContDiff ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The smooth finite-gap realization preserves the original real form pointwise. -/
theorem sourceFiniteGapPhysicalPair_real (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (x : ℝ) :
    (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 x =
      conj ((sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x) := by
  have hreal (n : ℤ) : φ.val.snd n = conj (φ.val.fst (-n)) := φ.property n
  simp only [sourceFiniteGapPhysicalPair,periodOneSynthesis_eq_tsum,Complex.conj_tsum]
  simp only [hreal,map_mul]
  have he := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => conj (φ.val.fst n)*conj (wave (2*n) x))
  simpa only [Equiv.neg_apply,mul_neg,wave_neg,starRingEnd_self_apply] using he

/-- The classical Hamiltonian velocity of the actual smooth finite-gap representative. -/
def sourceFiniteGapPhysicalNLSVectorField (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (ℝ → ℂ) × (ℝ → ℂ) :=
  classicalNLSVectorField (sourceFiniteGapPhysicalPair hp hp1 φ hf).1
    (sourceFiniteGapPhysicalPair hp hp1 φ hf).2

/-- Smooth periodic physical directions give the first variational derivative at every finite-gap source. -/
theorem hasDerivAt_sourceFiniteGapNLSHamiltonian_three_fst
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian
      (fun x => (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x+z*h x)
      (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 3)
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSEnergyGradient
        (sourceFiniteGapPhysicalPair hp hp1 φ hf).1
        (sourceFiniteGapPhysicalPair hp hp1 φ hf).2).1 x) 0 :=
  hasDerivAt_classicalNLSHamiltonian_three_fst _ _ h
    (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).1
    (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).2 hh
    (periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf).1
    (periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf).2 hph

/-- The second physical variation has the opposite cross-component Hamiltonian role. -/
theorem hasDerivAt_sourceFiniteGapNLSHamiltonian_three_snd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian
      (sourceFiniteGapPhysicalPair hp hp1 φ hf).1
      (fun x => (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 x+z*h x) 3)
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSEnergyGradient
        (sourceFiniteGapPhysicalPair hp hp1 φ hf).1
        (sourceFiniteGapPhysicalPair hp hp1 φ hf).2).2 x) 0 :=
  hasDerivAt_classicalNLSHamiltonian_three_snd _ _ h
    (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).1
    (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).2 hh
    (periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf).1
    (periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf).2 hph

/-- The physical finite-gap NLS field is smooth and period one in both components. -/
theorem sourceFiniteGapPhysicalNLSVectorField_regular (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (ContDiff ℝ ∞ (sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).1 ∧
      ContDiff ℝ ∞ (sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).2) ∧
    (Function.Periodic (sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).1 1 ∧
      Function.Periodic (sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).2 1) :=
  ⟨contDiff_classicalNLSVectorField _ _ (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).1
      (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).2,
    periodic_classicalNLSVectorField _ _ (periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf).1
      (periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf).2⟩

/-- The finite-gap physical velocity preserves the real form. -/
theorem sourceFiniteGapPhysicalNLSVectorField_real (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (x : ℝ) :
    (sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).2 x =
      conj ((sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).1 x) := by
  unfold sourceFiniteGapPhysicalNLSVectorField
  rw [show (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 =
    fun y => conj ((sourceFiniteGapPhysicalPair hp hp1 φ hf).1 y) from
      funext (sourceFiniteGapPhysicalPair_real hp hp1 φ hf)]
  exact classicalNLSVectorField_real _ x

/-- The first physical velocity has exactly the scalar defocusing NLS normalization. -/
theorem sourceFiniteGapPhysicalNLSVectorField_scalar (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (x : ℝ) :
    I*(sourceFiniteGapPhysicalNLSVectorField hp hp1 φ hf).1 x =
      -deriv (deriv (sourceFiniteGapPhysicalPair hp hp1 φ hf).1) x +
        2*(‖(sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x‖^2 : ℝ)*
          (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x := by
  unfold sourceFiniteGapPhysicalNLSVectorField
  rw [show (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 =
    fun y => conj ((sourceFiniteGapPhysicalPair hp hp1 φ hf).1 y) from
      funext (sourceFiniteGapPhysicalPair_real hp hp1 φ hf)]
  exact classicalNLSVectorField_scalar _ x

end NLS.ZakharovShabat
