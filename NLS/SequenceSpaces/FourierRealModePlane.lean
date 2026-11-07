import NLS.SequenceSpaces.FourierRealZeroCoordinates
import NLS.SequenceSpaces.FourierRealZeroDecomposition

/-! Literal complex mode planes in the physical Fourier real form.
The positive coefficient is c and the negative coefficient is conjugate c;
there is no square-root or action normalization in this insertion. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def realSineDirection (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+) :
    fourierRealZeroSubmodule w p :=
  fourierRealZeroProjection w hw (zeroModeSingle w (n:ℤ) (by exact_mod_cast n.ne_zero) (2*I))

theorem realCosineDirection_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ+) (k : ℤ) :
    (realCosineDirection (p := p) w hw n).val.val.val k=
      (if k=(n:ℤ) then 1 else 0)+(if k=-(n:ℤ) then 1 else 0) := by
  have hn : -(n:ℤ) ≠ (n:ℤ) := by
    have hp : (0:ℤ)<n := by exact_mod_cast n.pos
    omega
  change (fourierRealZeroProjection w hw (zeroModeSingle w (n:ℤ) _ 2)).val.val.val k=_
  rw [fourierRealZeroProjection_apply,zeroModeSingle_apply,zeroModeSingle_apply]
  by_cases hk : k=(n:ℤ)
  · subst k; norm_num [hn,map_ofNat]
  · by_cases hm : k=-(n:ℤ)
    · subst k; norm_num [hn,map_ofNat]
    · have hneg : -k ≠ (n:ℤ) := by omega
      simp [hk,hm,hneg]

theorem realSineDirection_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ+) (k : ℤ) :
    (realSineDirection (p := p) w hw n).val.val.val k=
      (if k=(n:ℤ) then I else 0)-(if k=-(n:ℤ) then I else 0) := by
  have hn : -(n:ℤ) ≠ (n:ℤ) := by
    have hp : (0:ℤ)<n := by exact_mod_cast n.pos
    omega
  change (fourierRealZeroProjection w hw (zeroModeSingle w (n:ℤ) _ (2*I))).val.val.val k=_
  rw [fourierRealZeroProjection_apply,zeroModeSingle_apply,zeroModeSingle_apply]
  by_cases hk : k=(n:ℤ)
  · subst k
    norm_num [hn,map_ofNat]
    ring
  · by_cases hm : k=-(n:ℤ)
    · subst k
      norm_num [hn,map_ofNat]
      ring
    · have hneg : -k ≠ (n:ℤ) := by omega
      simp [hk,hm,hneg]

def fourierRealModeCLM (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+) :
    ℂ →L[ℝ] fourierRealZeroSubmodule w p :=
  Complex.reCLM.smulRight (realCosineDirection w hw n)+
    Complex.imCLM.smulRight (realSineDirection w hw n)

theorem fourierRealModeCLM_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ+) (c : ℂ) (k : ℤ) :
    (fourierRealModeCLM (p := p) w hw n c).val.val.val k=
      (if k=(n:ℤ) then c else 0)+(if k=-(n:ℤ) then (starRingEnd ℂ) c else 0) := by
  have hn : -(n:ℤ) ≠ (n:ℤ) := by
    have hp : (0:ℤ)<n := by exact_mod_cast n.pos
    omega
  change (c.re:ℂ)*(realCosineDirection w hw n).val.val.val k+
    (c.im:ℂ)*(realSineDirection w hw n).val.val.val k=_
  rw [realCosineDirection_apply,realSineDirection_apply]
  by_cases hk : k=(n:ℤ)
  · subst k; simp only [ite_true,if_neg (Ne.symm hn),add_zero,sub_zero,mul_one]
    exact Complex.re_add_im c
  · by_cases hm : k=-(n:ℤ)
    · subst k; simp only [if_neg hn,ite_true,zero_add,zero_sub,mul_one]
      apply Complex.ext <;> simp
    · simp [hk,hm]

/-- Replace one conjugate pair while retaining every other Fourier coefficient. -/
def fourierRealModeReplace (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ+) (z : fourierRealZeroSubmodule w p) (c : ℂ) : fourierRealZeroSubmodule w p :=
  z+fourierRealModeCLM w hw n (c-z.val.val.val (n:ℤ))

theorem fourierRealModeReplace_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ+) (z : fourierRealZeroSubmodule w p) (c : ℂ) (k : ℤ) :
    (fourierRealModeReplace w hw n z c).val.val.val k=
      if k=(n:ℤ) then c else if k=-(n:ℤ) then (starRingEnd ℂ) c else z.val.val.val k := by
  have hn : -(n:ℤ) ≠ (n:ℤ) := by
    have hp : (0:ℤ)<n := by exact_mod_cast n.pos
    omega
  change z.val.val.val k+(fourierRealModeCLM w hw n (c-z.val.val.val (n:ℤ))).val.val.val k=_
  rw [fourierRealModeCLM_apply]
  by_cases hk : k=(n:ℤ)
  · subst k; simp [Ne.symm hn]
  · by_cases hm : k=-(n:ℤ)
    · subst k; simp [hn,map_sub,z.property (n:ℤ)]
    · simp [hk,hm]

theorem fourierRealModeReplace_products (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ+) (z : fourierRealZeroSubmodule w p) (c : ℂ)
    (hc : c*(starRingEnd ℂ) c=z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ)))
    (m : ℕ+) :
    (fourierRealModeReplace w hw n z c).val.val.val (m:ℤ)*
      (fourierRealModeReplace w hw n z c).val.val.val (-(m:ℤ))=
      z.val.val.val (m:ℤ)*z.val.val.val (-(m:ℤ)) := by
  have hn : (0:ℤ)<n := by exact_mod_cast n.pos
  have hm : (0:ℤ)<m := by exact_mod_cast m.pos
  rw [fourierRealModeReplace_apply,fourierRealModeReplace_apply]
  by_cases h : (m:ℤ)=(n:ℤ)
  · have h2 : -(n:ℤ)≠(n:ℤ) := by omega
    simp only [h,ite_true,if_neg h2]
    rw [z.property (n:ℤ)]
    exact hc
  · have h1 : (m:ℤ)≠-(n:ℤ) := by omega
    have h2 : -(m:ℤ)≠(n:ℤ) := by omega
    have h3 : -(m:ℤ)≠-(n:ℤ) := by omega
    simp only [if_neg h,if_neg h1,if_neg h2,if_neg h3]

end NLS.WeightedCoeff
