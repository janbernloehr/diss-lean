import NLS.KdV.HillInverseSobolevBound

/-! # Coefficient-preserving native integer Sobolev inclusions and exact lower norm normalization. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem hillIntegerWeight_mono_order (i j : ℕ) (hij : i ≤ j) (k : ℤ) :
    (hillIntegerWeight i).doubleIndex.toWeight k ≤ (hillIntegerWeight j).doubleIndex.toWeight k := by
  simp only [SpectralWeight.doubleIndex_apply,hillIntegerWeight_apply]
  exact pow_le_pow_right₀ (by nlinarith [Real.pi_pos,abs_nonneg (k : ℝ)] : 1 ≤ 1+2*Real.pi*|(k : ℝ)|) hij

def hillNativeIntegerLower (M j : ℕ) (hj : j ≤ M) :
    WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2 →L[ℂ]
      WeightedCoeff (hillIntegerWeight j).doubleIndex.toWeight 2 :=
  WeightedCoeff.inclusionCLM _ _ (hillIntegerWeight_mono_order j M hj)

@[simp] theorem hillNativeIntegerLower_apply (M j : ℕ) (hj : j ≤ M)
    (p : WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2) (k : ℤ) :
    (hillNativeIntegerLower M j hj p).val k = p.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ p k

theorem hillScalarSobolevLower_comp (M l j : ℕ) (hl : l ≤ M) (hj : j ≤ l)
    (a : ScalarSobolev M) :
    hillScalarSobolevLower l j hj (hillScalarSobolevLower M l hl a) =
      hillScalarSobolevLower M j (hj.trans hl) a := by
  apply Subtype.ext
  funext k
  simp only [hillScalarSobolevLower_apply]

theorem hillSobolevHamiltonianFamily_lower (M l j : ℕ) (hl : l ≤ M) (hj : j ≤ l)
    (a : ScalarSobolev M) :
    hillSobolevHamiltonianFamily l (hillScalarSobolevLower M l hl a) j =
      hillSobolevHamiltonianFamily M a j := by
  simp only [hillSobolevHamiltonianFamily,dif_pos hj,dif_pos (hj.trans hl),hillSobolevHamiltonianAt]
  split_ifs with hz
  · rw [hillScalarSobolevLower_comp M l 0 hl (Nat.zero_le l)]
  · rw [hillScalarSobolevLower_comp M l j hl hj]

theorem hillNativeIntegerToScalar_lower (M j : ℕ) (hj : j ≤ M)
    (p : WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2) :
    hillNativeIntegerToScalar j (hillNativeIntegerLower M j hj p) =
      hillScalarSobolevLower M j hj (hillNativeIntegerToScalar M p) := by
  apply Subtype.ext
  funext k
  simp only [hillNativeIntegerToScalar_apply,hillNativeIntegerLower_apply,hillScalarSobolevLower_apply]


def hillRealNativeIntegerLower (M j : ℕ) (hj : j ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    RealHillWeightedPotential (hillIntegerWeight j) :=
  ⟨hillNativeIntegerLower M j hj p.val,fun k => by
    simpa only [SpectralWeight.toCoeff_apply,hillNativeIntegerLower_apply] using p.property k⟩

theorem hillRealNativeIntegerLower_mean_zero (M j : ℕ) (hj : j ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    (hillRealNativeIntegerLower M j hj p).val.val 0 = 0 := by
  simpa only [hillRealNativeIntegerLower,hillNativeIntegerLower_apply] using hmean

theorem hillNativeHamiltonianFamily_lower (M l j : ℕ) (hl : l ≤ M) (hj : j ≤ l)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    hillSobolevHamiltonianFamily l
        (hillNativeIntegerToScalar l (hillRealNativeIntegerLower M l hl p).val) j =
      hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val) j := by
  change hillSobolevHamiltonianFamily l (hillNativeIntegerToScalar l (hillNativeIntegerLower M l hl p.val)) j = _
  rw [hillNativeIntegerToScalar_lower,hillSobolevHamiltonianFamily_lower M l j hl hj]

theorem hillPeriodOneUnitPotential_lower (M j : ℕ) (hj : j ≤ M)
    (p : WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2) :
    hillPeriodOneUnitPotential (hillIntegerWeight j) (hillNativeIntegerLower M j hj p) =
      hillPeriodOneUnitPotential (hillIntegerWeight M) p := by
  apply hillPeriodOneUnitPotential_eq_of_coeff_eq
  intro k
  exact hillNativeIntegerLower_apply M j hj p k

theorem hillNativeIntegerLower_norm_sq (M j : ℕ) (hj : j ≤ M)
    (p : WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2) :
    HasSum (fun k : ℤ => (1+|2*Real.pi*(k : ℝ)|)^(2*j)*‖p.val k‖^2)
      (‖hillNativeIntegerLower M j hj p‖^2) := by
  have h := hillPeriodOne_sobolev_norm_sq j (hillNativeIntegerLower M j hj p)
  simp only [hillNativeIntegerLower_apply] at h
  convert! h using 1

end NLS.KdV
