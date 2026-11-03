import NLS.KdV.HillNormalizedPhase

/-! The actual inverse of I_lambda-S_lambda on the entire normalized
Hilbert space, with exact norm bound TWO in the proved high-energy range. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- The actual total normalized inverse family. -/
def hillNormalizedInverse (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2) (z : ℂ) :
    Coeff 2 →L[ℂ] Coeff 2 := Ring.inverse (hillNormalizedPhase z-hillHalfSandwich r q z)

/-- When the actual normalized perturbation has norm at most one half, the
ACTUAL I_lambda-S_lambda inverse is two-sided and has norm at most TWO. -/
theorem hillNormalizedInverse_spec (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    (hillNormalizedPhase z-hillHalfSandwich r q z).comp (hillNormalizedInverse r q z) =
        ContinuousLinearMap.id ℂ (Coeff 2) ∧
    (hillNormalizedInverse r q z).comp (hillNormalizedPhase z-hillHalfSandwich r q z) =
        ContinuousLinearMap.id ℂ (Coeff 2) ∧
    ‖hillNormalizedInverse r q z‖ ≤ 2 := by
  obtain ⟨h1,h2⟩ := hillNormalizedPhase_inverse_spec n hn z hz
  have hnear : ‖(hillNormalizedPhaseInverse z).comp (-hillHalfSandwich r q z)‖ ≤ 1/2 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_neg]
    exact (mul_le_mul_of_nonneg_left hS (norm_nonneg _)).trans
      (by have h := norm_hillNormalizedPhaseInverse_le z;nlinarith)
  obtain ⟨K,hK1,hK2,hK⟩ := NLS.exists_inverse_norm_le_two_mul_of_perturbation
    (hillNormalizedPhase z) (hillNormalizedPhaseInverse z) (-hillHalfSandwich r q z) h1 h2 hnear
  have hK1' : (hillNormalizedPhase z-hillHalfSandwich r q z)*K = 1 := by
    change (hillNormalizedPhase z-hillHalfSandwich r q z).comp K = ContinuousLinearMap.id ℂ (Coeff 2)
    simpa only [sub_eq_add_neg] using hK1
  have hK2' : K*(hillNormalizedPhase z-hillHalfSandwich r q z) = 1 := by
    change K.comp (hillNormalizedPhase z-hillHalfSandwich r q z) = ContinuousLinearMap.id ℂ (Coeff 2)
    simpa only [sub_eq_add_neg] using hK2
  let U : (Coeff 2 →L[ℂ] Coeff 2)ˣ :=
    ⟨hillNormalizedPhase z-hillHalfSandwich r q z,K,hK1',hK2'⟩
  have he : hillNormalizedInverse r q z = K := Ring.inverse_unit U
  rw [he]
  exact ⟨hK1',hK2',hK.trans (by have h := norm_hillNormalizedPhaseInverse_le z;nlinarith)⟩

/-- The actual normalized resolvent difference identity on the FULL Hilbert
space. Every factor is the constructed original operator, with its order retained. -/
theorem hillNormalizedInverse_sub_phaseInverse (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    hillNormalizedInverse r q z-hillNormalizedPhaseInverse z =
      (hillNormalizedInverse r q z).comp ((hillHalfSandwich r q z).comp (hillNormalizedPhaseInverse z)) := by
  have hfree : hillNormalizedPhase z*hillNormalizedPhaseInverse z = 1 :=
    (hillNormalizedPhase_inverse_spec n hn z hz).1
  have hpert : hillNormalizedInverse r q z*(hillNormalizedPhase z-hillHalfSandwich r q z) = 1 :=
    (hillNormalizedInverse_spec r q n hn z hz hS).2.1
  change hillNormalizedInverse r q z-hillNormalizedPhaseInverse z =
    hillNormalizedInverse r q z*(hillHalfSandwich r q z*hillNormalizedPhaseInverse z)
  calc
    _ = hillNormalizedInverse r q z*(hillNormalizedPhase z*hillNormalizedPhaseInverse z)-
        (hillNormalizedInverse r q z*(hillNormalizedPhase z-hillHalfSandwich r q z))*
          hillNormalizedPhaseInverse z := by rw [hfree,hpert,mul_one,one_mul]
    _ = _ := by noncomm_ring

/-- The normalized inverse difference is bounded by twice the ACTUAL
normalized rough-potential perturbation norm. -/
theorem norm_hillNormalizedInverse_sub_phaseInverse_le (r : ℝ)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    ‖hillNormalizedInverse r q z-hillNormalizedPhaseInverse z‖ ≤ 2*‖hillHalfSandwich r q z‖ := by
  rw [hillNormalizedInverse_sub_phaseInverse r q n hn z hz hS]
  calc
    _ ≤ ‖hillNormalizedInverse r q z‖*(‖hillHalfSandwich r q z‖*‖hillNormalizedPhaseInverse z‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 2*(‖hillHalfSandwich r q z‖*1) :=
      mul_le_mul (hillNormalizedInverse_spec r q n hn z hz hS).2.2
        (mul_le_mul_of_nonneg_left (norm_hillNormalizedPhaseInverse_le z) (norm_nonneg _))
        (by positivity) (by norm_num)
    _ = _ := by rw [mul_one]

end NLS.KdV
