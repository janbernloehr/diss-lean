import NLS.SequenceSpaces.FourierRealZeroProjection

/-! Every complex zero-mode Fourier sequence decomposes uniquely into
physical real and imaginary Fourier parts. The bounded physical real
projection annihilates imaginary multiples of physical real vectors. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem fourierRealZeroProjection_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) (k : ℤ) :
    (fourierRealZeroProjection w hw a).val.val.val k =
      (1/2:ℂ)*(a.val.val k+(starRingEnd ℂ) (a.val.val (-k))) :=
  zeroModeSymmetricPartCLM_apply w hw a k

/-- The real and imaginary physical Fourier parts recover every complex vector. -/
theorem fourierRealZeroProjection_decomposition (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) :
    (fourierRealZeroProjection w hw a : zeroModeSubmodule w p)+
      I • (fourierRealZeroProjection w hw (-I • a) : zeroModeSubmodule w p)=a := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change (fourierRealZeroProjection w hw a).val.val.val k+
    I*(fourierRealZeroProjection w hw (-I • a)).val.val.val k = a.val.val k
  rw [fourierRealZeroProjection_apply,fourierRealZeroProjection_apply]
  change (1/2:ℂ)*(a.val.val k+(starRingEnd ℂ) (a.val.val (-k)))+
    I*((1/2:ℂ)*(-I*a.val.val k+(starRingEnd ℂ) (-I*a.val.val (-k))))=a.val.val k
  rw [map_mul,map_neg,Complex.conj_I]
  ring_nf
  simp only [I_sq]
  ring

/-- The physical real projection kills imaginary multiples of physical real vectors. -/
theorem fourierRealZeroProjection_I_smul (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : fourierRealZeroSubmodule w p) :
    fourierRealZeroProjection w hw (I • a.val)=0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [fourierRealZeroProjection_apply]
  change (1/2:ℂ)*(I*a.val.val.val k+(starRingEnd ℂ) (I*a.val.val.val (-k)))=0
  rw [map_mul,Complex.conj_I,a.property k,Complex.conj_conj]
  ring

end NLS.WeightedCoeff
