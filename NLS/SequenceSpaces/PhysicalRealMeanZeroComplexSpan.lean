import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted
import NLS.SequenceSpaces.ConjugateReflection

/-! # The physical real mean-zero form spans the original complex mean-zero space

The explicit real and imaginary Fourier-reflection parts preserve the
original weighted space and zero coefficient. Hence complex covectors are
fixed by their physical real mean-zero restrictions.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- Every original complex mean-zero direction is a+i*b with a,b genuine
physical real mean-zero directions in the SAME original weighted space. -/
theorem exists_physicalRealMeanZeroWeighted_decomposition (w : Weight)
    (hw : ∀ n : ℤ, w (-n)=w n) (h : WeightedCoeff w 2) (hm : h.val 0=0) :
    ∃ a b : physicalRealMeanZeroWeightedSubmodule w, h = a.val+I • b.val := by
  let J := WeightedCoeff.conjugateReflection (p := 2) w hw
  let a := (1/2 : ℂ) • (h+J h)
  let b := (-I/2 : ℂ) • (h-J h)
  have ha : a ∈ physicalRealMeanZeroWeightedSubmodule w := by
    constructor
    · intro j
      change (1/2 : ℂ)*(h.val (-j)+(J h).val (-j)) =
        conj ((1/2 : ℂ)*(h.val j+(J h).val j))
      simp only [J,WeightedCoeff.conjugateReflection_apply,neg_neg,map_mul,map_div₀,
        map_one,map_ofNat,map_add,conj_conj]
      ring
    · change (1/2 : ℂ)*(h.val 0+(J h).val 0)=0
      simp only [J,WeightedCoeff.conjugateReflection_apply,neg_zero,hm,map_zero,add_zero,mul_zero]
  have hb : b ∈ physicalRealMeanZeroWeightedSubmodule w := by
    constructor
    · intro j
      change (-I/2 : ℂ)*(h.val (-j)-(J h).val (-j)) =
        conj ((-I/2 : ℂ)*(h.val j-(J h).val j))
      simp only [J,WeightedCoeff.conjugateReflection_apply,neg_neg,map_mul,map_div₀,
        map_neg,Complex.conj_I,map_ofNat,map_sub,conj_conj]
      ring
    · change (-I/2 : ℂ)*(h.val 0-(J h).val 0)=0
      simp only [J,WeightedCoeff.conjugateReflection_apply,neg_zero,hm,map_zero,sub_self,mul_zero]
  refine ⟨⟨a,ha⟩,⟨b,hb⟩,?_⟩
  change h=(1/2 : ℂ) • (h+J h)+I • ((-I/2 : ℂ) • (h-J h))
  rw [smul_smul]
  have hi : (I : ℂ)*(-I/2)=1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
  rw [hi]
  module

/-- Physical real mean-zero first variations determine every complex
mean-zero value of the original bounded complex differential. -/
theorem clm_eq_on_meanZero_of_physical_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (w : Weight) (hw : ∀ n : ℤ, w (-n)=w n)
    (L M : WeightedCoeff w 2 →L[ℂ] F)
    (he : ∀ a : physicalRealMeanZeroWeightedSubmodule w, L a.val = M a.val)
    (h : WeightedCoeff w 2) (hm : h.val 0=0) : L h=M h := by
  obtain ⟨a,b,hab⟩ := exists_physicalRealMeanZeroWeighted_decomposition w hw h hm
  calc
    _ = L a.val+I • L b.val := by rw [hab,map_add,map_smul]
    _ = M a.val+I • M b.val := by rw [he a,he b]
    _ = _ := by rw [hab,map_add,map_smul]

end NLS
