import NLS.KdV.HillFreeSpectralImaginaryDerivative
import NLS.KdV.HillUnitWeightLift
import NLS.Poisson.GardnerFourierModes

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate ENNReal
namespace NLS.KdV

/-- The literal ORIGINAL real Fourier pair at the positive physical mode. -/
def hillOriginalFourierPair (n : ℕ+) (z : ℂ) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillUnitWeightLift 2 (lp.single 2 (2*(n : ℤ)) z+lp.single 2 (-(2*(n : ℤ))) (conj z))

theorem hillOriginalFourierPair_mem_real (n : ℕ+) (z : ℂ) :
    hillOriginalFourierPair n z ∈ hillRealSourceSubmodule := by
  constructor
  · rw [hillOriginalFourierPair,toCoeff_hillUnitWeightLift]
    apply (Coeff.paritySubspace (p := 2) 0).add_mem
    · apply Coeff.single_mem_paritySubspace
      omega
    · apply Coeff.single_mem_paritySubspace
      omega
  · intro j
    have h1 : -j = 2*(n : ℤ) ↔ j = -(2*(n : ℤ)) := by omega
    have h2 : -j = -(2*(n : ℤ)) ↔ j = 2*(n : ℤ) := by omega
    simp only [hillOriginalFourierPair,toCoeff_hillUnitWeightLift,lp.coeFn_add,Pi.add_apply,
      lp.single_apply,Pi.single_apply,h1,h2,map_add]
    have hn : 2*(n : ℤ) ≠ -(2*(n : ℤ)) := by have := n.pos; omega
    by_cases ha : j = 2*(n : ℤ) <;> by_cases hb : j = -(2*(n : ℤ)) <;>
      simp [ha,hb,hn,Ne.symm hn]

theorem hillOriginalFourierPair_mean_zero (n : ℕ+) (z : ℂ) :
    (hillOriginalFourierPair n z).val 0 = 0 := by
  have hn0 : 2*(n : ℤ) ≠ 0 := by have := n.pos; omega
  simp [hillOriginalFourierPair,hn0]

/-- The actual positive Fourier pair as a direction in the ORIGINAL
real mean-zero Banach domain. -/
def hillOriginalFourierDirection (n : ℕ+) (z : ℂ) : hillRealMeanZeroSourceSubmodule :=
  ⟨⟨hillOriginalFourierPair n z,hillOriginalFourierPair_mem_real n z⟩,
    (mem_hillRealMeanZeroSourceSubmodule _).mpr (hillOriginalFourierPair_mean_zero n z)⟩

theorem hillOriginalFourierDirection_apply (n : ℕ+) (z : ℂ) (j : ℤ) :
    (hillOriginalFourierDirection n z).val.val.val j =
      (if 2*(n : ℤ) = j then z else 0)+(if -(2*(n : ℤ)) = j then conj z else 0) := by
  simp only [hillOriginalFourierDirection,hillOriginalFourierPair,hillUnitWeightLift_apply,
    lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,eq_comm]

/-- The native H-minus-one inclusion retains exactly the two raw unit-period modes. -/
theorem hillOriginalFourierDirection_hminus_apply (n : ℕ+) (z : ℂ) (j : ℤ) :
    (hillOriginalRealHminusInclusion (hillOriginalFourierDirection n z).val).val j =
      (if (n : ℤ) = j then z else 0)+(if -(n : ℤ) = j then conj z else 0) := by
  change (hillOriginalHminusSource (hillOriginalFourierDirection n z).val.val).val j = _
  rw [hillOriginalHminusSource_apply,hillOriginalFourierDirection_apply]
  have h1 : 2*(n : ℤ) = 2*j ↔ (n : ℤ) = j := by omega
  have h2 : -(2*(n : ℤ)) = 2*j ↔ -(n : ℤ) = j := by omega
  simp only [h1,h2]

/-- The original cosine direction is exactly the symmetric native mode. -/
theorem hillOriginalFourierDirection_cosine_hminus (n : ℕ+) :
    hillOriginalRealHminusInclusion (hillOriginalFourierDirection n 1).val =
      NLS.Poisson.hminusCosineMode n := by
  apply Subtype.ext
  funext j
  simp only [hillOriginalFourierDirection_hminus_apply,map_one,NLS.Poisson.hminusCosineMode_apply]

/-- The ORIGINAL raw coefficient map on the real mean-zero Banach source. -/
def hillOriginalRawSourceCLM : hillRealMeanZeroSourceSubmodule →L[ℝ] Coeff 2 :=
  (SpectralWeight.one.toCoeff.restrictScalars ℝ).comp
    (hillRealSourceSubmodule.subtypeL.comp hillRealMeanZeroSourceSubmodule.subtypeL)

/-- Passing to literal raw coefficients preserves the original L2 norm. -/
theorem norm_hillOriginalRawSourceCLM (h : hillRealMeanZeroSourceSubmodule) :
    ‖hillOriginalRawSourceCLM h‖ = ‖h‖ := by
  change ‖SpectralWeight.one.toCoeff h.val.val‖ = ‖h.val.val‖
  rw [←norm_hillUnitWeightLift 2 (SpectralWeight.one.toCoeff h.val.val),hillUnitWeightLift_toCoeff]

/-- Raw coefficients of a physical Fourier direction are precisely its
original even positive mode and conjugate negative mode. -/
theorem hillOriginalRawSourceCLM_fourierDirection (n : ℕ+) (z : ℂ) :
    hillOriginalRawSourceCLM (hillOriginalFourierDirection n z) =
      lp.single 2 (2*(n : ℤ)) z+lp.single 2 (-(2*(n : ℤ))) (conj z) := by
  change SpectralWeight.one.toCoeff (hillOriginalFourierPair n z) = _
  rw [hillOriginalFourierPair,toCoeff_hillUnitWeightLift]

end NLS.KdV
