import NLS.Fourier.PeriodicH1Multiplication

/-! Operator-norm linear dependence of the actual singular multiplication on its potential. -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)]

/-- Physical singular multiplication is additive in the potential. -/
theorem hminusOneProduct_add_left (q v : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    hminusOneProduct (q+v) f = hminusOneProduct q f+hminusOneProduct v f := by
  apply (sobolevDualIsometry (p := 2) (q := 2) 1 (by norm_num)).injective
  ext g
  simp only [hminusOneProduct_duality,map_add,_root_.add_apply]

/-- Physical singular multiplication is complex linear in the potential. -/
theorem hminusOneProduct_smul_left (c : ℂ) (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    hminusOneProduct (c • q) f = c • hminusOneProduct q f := by
  apply (sobolevDualIsometry (p := 2) (q := 2) 1 (by norm_num)).injective
  ext g
  simp only [hminusOneProduct_duality,map_smul,_root_.smul_apply]

/-- The potential-to-operator map uses the full original H-minus-one norm. -/
def hminusOneMultiplicationFamily : FourierLebesgueSpace L (-1) 2 →L[ℂ]
    (FourierLebesgueSpace L 1 2 →L[ℂ] FourierLebesgueSpace L (-1) 2) :=
  LinearMap.mkContinuous
    { toFun := hminusOneMultiplication
      map_add' := fun q v => by ext f; exact hminusOneProduct_add_left q v f
      map_smul' := fun c q => by ext f; exact hminusOneProduct_smul_left c q f }
    (3*WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num))
    (fun q => ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by norm_num)
        (WeightedCoeff.sobolevEmbeddingConstant_nonneg 2 (by norm_num))) (norm_nonneg q))
      (norm_hminusOneProduct_le q))

@[simp] theorem hminusOneMultiplicationFamily_apply (q : FourierLebesgueSpace L (-1) 2) :
    hminusOneMultiplicationFamily q = hminusOneMultiplication q := rfl

end NLS.Fourier.PeriodicFourierLebesgue
