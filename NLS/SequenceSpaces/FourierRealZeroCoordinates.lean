import NLS.SequenceSpaces.FourierRealZeroProjection
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.HalfFourierEquiv

/-! Continuous coefficient evaluations and literal finite Fourier
directions on the physical real zero-mode Banach spaces, including infinity. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def fourierRealZeroEvalCLM (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) :
    fourierRealZeroSubmodule w p →L[ℝ] ℂ :=
  (evalCLM w p k).restrictScalars ℝ |>.comp
    (((zeroModeSubmodule w p).subtypeL.restrictScalars ℝ).comp (fourierRealZeroSubmodule w p).subtypeL)

theorem fourierRealZeroEvalCLM_apply (w : Weight) (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    fourierRealZeroEvalCLM w p k a=a.val.val.val k := rfl

def zeroModeSingle (w : Weight) (k : ℤ) (hk : k ≠ 0) (c : ℂ) : zeroModeSubmodule w p :=
  ⟨single w k c,by
    change (single w k c).val 0=0
    simp only [single_val,Pi.single_apply,if_neg (Ne.symm hk)]⟩

theorem zeroModeSingle_apply (w : Weight) (k : ℤ) (hk : k ≠ 0) (c : ℂ) (j : ℤ) :
    (zeroModeSingle (p := p) w k hk c).val.val j=(Pi.single k c : ℤ → ℂ) j := single_val (p := p) w k c j

def realCosineDirection (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+) :
    fourierRealZeroSubmodule w p :=
  fourierRealZeroProjection w hw (zeroModeSingle w (n:ℤ) (by exact_mod_cast n.ne_zero) 2)

theorem realCosineDirection_positive (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+) :
    (realCosineDirection (p := p) w hw n).val.val.val (n:ℤ)=1 := by
  have hn : -(n:ℤ) ≠ (n:ℤ) := by
    have hp : (0:ℤ) < n := by exact_mod_cast n.pos
    omega
  change (zeroModeSymmetricPartCLM w hw (zeroModeSingle w (n:ℤ) _ 2)).val.val (n:ℤ)=1
  rw [zeroModeSymmetricPartCLM_apply,zeroModeSingle_apply,zeroModeSingle_apply]
  simp only [Pi.single_apply,ite_true,if_neg hn,map_zero,add_zero]
  norm_num

theorem realCosineDirection_negative (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+) :
    (realCosineDirection (p := p) w hw n).val.val.val (-(n:ℤ))=1 := by
  rw [(realCosineDirection (p := p) w hw n).property (n:ℤ),realCosineDirection_positive,map_one]

theorem halfFourierSymbol_ne_zero (k : ℤ) : halfFourierSymbol k ≠ 0 := by
  intro he
  have h := halfFourierSymbol_mul_inverse k
  rw [he,zero_mul] at h
  norm_num at h

end NLS.WeightedCoeff
