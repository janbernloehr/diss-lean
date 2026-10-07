import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapNLSHamiltonians

/-! # Calibration of the H¹ energy on the actual finite-gap source

The physical H¹ Hamiltonian agrees with Appendix H's third Hamiltonian for
all finite-gap sources, independently of the original coefficient exponent.
The Sobolev representative retains the original raw Fourier coefficients.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual finite-gap source as an H¹ pair, with unchanged raw coefficients. -/
def sourceFiniteGapSobolevPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ScalarDomain 2 × ScalarDomain 2 :=
  (⟨_, (sourceFiniteGap_mem_H1 hp hp1 φ hf).1⟩,
   ⟨_, (sourceFiniteGap_mem_H1 hp hp1 φ hf).2⟩)

/-- The full H¹ construction and the smooth finite-gap construction give the same functions. -/
theorem periodOneSobolevSynthesis_sourceFiniteGapSobolevPair
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (fun x : ℝ => periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).1
      (x : AddCircle (2 : ℝ))) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 ∧
    (fun x : ℝ => periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).2
      (x : AddCircle (2 : ℝ))) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 := by
  constructor
  · change periodOneSynthesis (WeightedCoeff.sobolevToL1CLM 2 (by simp)
      (sourceFiniteGapSobolevPair hp hp1 φ hf).1) = periodOneSynthesis _
    congr 1
    ext n
    exact WeightedCoeff.sobolevToL1CLM_apply _ _ _ n
  · change periodOneSynthesis (WeightedCoeff.sobolevToL1CLM 2 (by simp)
      (sourceFiniteGapSobolevPair hp hp1 φ hf).2) = periodOneSynthesis _
    congr 1
    ext n
    exact WeightedCoeff.sobolevToL1CLM_apply _ _ _ n

/-- The analytic H¹ mass is exactly the first physical hierarchy Hamiltonian. -/
theorem periodOneSobolevMass_sourceFiniteGapSobolevPair
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    periodOneSobolevMass (sourceFiniteGapSobolevPair hp hp1 φ hf) =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 := by
  have h := periodOneSobolevMass_eq_integral
    (sourceFiniteGapSobolevPair hp hp1 φ hf).1 (sourceFiniteGapSobolevPair hp hp1 φ hf).2
  obtain ⟨ha, hb⟩ := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair hp hp1 φ hf
  change _ = ∫ x in (0 : ℝ)..1,
    (fun t : ℝ => periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).1
      (t : AddCircle (2 : ℝ))) x *
    (fun t : ℝ => periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).2
      (t : AddCircle (2 : ℝ))) x at h
  rw [ha, hb] at h
  exact h.trans (classicalNLSHamiltonian_one _ _).symm

/-- The analytic H¹ energy is exactly the third physical hierarchy Hamiltonian. -/
theorem periodOneSobolevHamiltonian_sourceFiniteGapSobolevPair
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair hp hp1 φ hf) =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3 := by
  have h := periodOneSobolevHamiltonian_eq_integral
    (sourceFiniteGapSobolevPair hp hp1 φ hf).1 (sourceFiniteGapSobolevPair hp hp1 φ hf).2
  obtain ⟨ha, hb⟩ := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair hp hp1 φ hf
  simp only [ha, hb] at h
  have hc := contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf
  have hp' := periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf
  rw [sourceFiniteGapNLSHamiltonian, classicalNLSHamiltonian_three _ _ hc.1 hc.2 hp'.1 hp'.2]
  convert h using 1
  apply intervalIntegral.integral_congr
  intro x _
  have ha' : periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).1
      (x : AddCircle (2 : ℝ)) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x := congrFun ha x
  have hb' : periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).2
      (x : AddCircle (2 : ℝ)) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 x := congrFun hb x
  dsimp only
  rw [ha', hb']

end NLS.ZakharovShabat
