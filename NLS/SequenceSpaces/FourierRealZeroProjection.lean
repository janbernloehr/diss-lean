import NLS.SequenceSpaces.FourierRealZeroSubmodule

/-! A bounded real linear projection onto the physical Fourier real form.
It preserves the zero mode and fixes every real Fourier sequence exactly. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def zeroModeSymmetricPartCLM (w : Weight) (hw : ∀ k, w (-k)=w k) :
    zeroModeSubmodule w p →L[ℝ] zeroModeSubmodule w p :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ _+zeroModeConjugationCLM w hw)

theorem zeroModeSymmetricPartCLM_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) (k : ℤ) :
    (zeroModeSymmetricPartCLM w hw a).val.val k=
      (1/2:ℂ)*(a.val.val k+(starRingEnd ℂ) (a.val.val (-k))) := by
  change ((1/2:ℝ) • (a+zeroModeConjugation w hw a)).val.val k=_
  rw [zeroMode_real_smul_val,zeroMode_add_val,zeroModeConjugation_apply]
  norm_num

theorem zeroModeSymmetricPartCLM_mem (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) : zeroModeSymmetricPartCLM w hw a ∈ fourierRealZeroSubmodule w p := by
  intro k
  rw [zeroModeSymmetricPartCLM_apply,zeroModeSymmetricPartCLM_apply,neg_neg,map_mul,map_add,
    Complex.conj_conj]
  simp only [map_div₀,map_one,map_ofNat]
  ring

def fourierRealZeroProjection (w : Weight) (hw : ∀ k, w (-k)=w k) :
    zeroModeSubmodule w p →L[ℝ] fourierRealZeroSubmodule w p :=
  (zeroModeSymmetricPartCLM w hw).codRestrict _ (zeroModeSymmetricPartCLM_mem w hw)

theorem fourierRealZeroProjection_coe (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) (ha : a ∈ fourierRealZeroSubmodule w p) :
    (fourierRealZeroProjection w hw a : zeroModeSubmodule w p)=a := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change (zeroModeSymmetricPartCLM w hw a).val.val k=a.val.val k
  rw [zeroModeSymmetricPartCLM_apply,ha k,Complex.conj_conj]
  ring

theorem fourierRealZeroProjection_inclusion (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : fourierRealZeroSubmodule w p) : fourierRealZeroProjection w hw a.val=a := by
  apply Subtype.ext
  exact fourierRealZeroProjection_coe w hw a.val a.property

end NLS.WeightedCoeff
