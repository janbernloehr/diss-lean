import NLS.SequenceSpaces.SobolevSignedActionSequence
import NLS.SequenceSpaces.WeightedSingle
import NLS.ComplexAnalysis.ActionRayDerivative

/-! # Actual real signed modes and their complete original action curves -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- A literal real mean-zero Fourier mode with amplitudes c and conj(c). -/
def physicalRealMeanZeroWeightedMode (w : Weight) (n : ℕ+) (c : ℂ) :
    physicalRealMeanZeroWeightedSubmodule w :=
  ⟨WeightedCoeff.single w (n : ℤ) c+WeightedCoeff.single w (-(n : ℤ)) (conj c),by
    constructor
    · intro j
      change (WeightedCoeff.single w (n : ℤ) c).val (-j)+
        (WeightedCoeff.single w (-(n : ℤ)) (conj c)).val (-j) =
        conj ((WeightedCoeff.single w (n : ℤ) c).val j+
          (WeightedCoeff.single w (-(n : ℤ)) (conj c)).val j)
      simp only [WeightedCoeff.single_val,Pi.single_apply,map_add]
      by_cases hj : j = (n : ℤ)
      · subst j
        have hn : (n : ℤ) ≠ -(n : ℤ) := by have := n.pos; omega
        simp [hn,hn.symm]
      · by_cases hjn : j = -(n : ℤ)
        · subst j
          have hn : (n : ℤ) ≠ -(n : ℤ) := by have := n.pos; omega
          simp [hn,hn.symm]
        · simp [hj,hjn,neg_eq_iff_eq_neg]
    · change (WeightedCoeff.single w (n : ℤ) c).val 0+
        (WeightedCoeff.single w (-(n : ℤ)) (conj c)).val 0=0
      simp only [WeightedCoeff.single_val,Pi.single_apply]
      have hn : (n : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
      simp [hn.symm]⟩

@[simp] theorem physicalRealMeanZeroWeightedMode_val (w : Weight) (n : ℕ+) (c : ℂ) (j : ℤ) :
    (physicalRealMeanZeroWeightedMode w n c).val.val j =
      (Pi.single (n : ℤ) c : ℤ → ℂ) j+(Pi.single (-(n : ℤ)) (conj c) : ℤ → ℂ) j := by
  change (WeightedCoeff.single w (n : ℤ) c).val j+
    (WeightedCoeff.single w (-(n : ℤ)) (conj c)).val j = _
  rw [WeightedCoeff.single_val,WeightedCoeff.single_val]

/-- The whole weighted action sequence along a genuine real signed mode
is a literal one-coordinate quadratic action curve, in the ORIGINAL norm. -/
theorem sobolevSignedActionSequence_mode_curve (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (n : ℕ+) (c : ℂ) (t : ℝ) :
    sobolevSignedActionSequence r s hrs
      (z+t • physicalRealMeanZeroWeightedMode (Weight.sobolev s) n c) =
      sobolevSignedActionSequence r s hrs z+
        ((t : ℂ)*(z.val.val n*conj c+c*z.val.val (-n))+(t : ℂ)^2*(c*conj c)) •
          WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1 := by
  apply Subtype.ext
  funext j
  change (sobolevSignedActionSequence r s hrs
    (z+t • physicalRealMeanZeroWeightedMode (Weight.sobolev s) n c)).val j =
    (sobolevSignedActionSequence r s hrs z).val j+
      ((t : ℂ)*(z.val.val n*conj c+c*z.val.val (-n))+(t : ℂ)^2*(c*conj c))*
        (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1).val j
  rw [sobolevSignedActionSequence_apply,sobolevSignedActionSequence_apply]
  change (if 0<j then
    (z.val.val j+(t : ℂ)*(physicalRealMeanZeroWeightedMode (Weight.sobolev s) n c).val.val j)*
      (z.val.val (-j)+(t : ℂ)*(physicalRealMeanZeroWeightedMode (Weight.sobolev s) n c).val.val (-j)) else 0) =
    (if 0<j then z.val.val j*z.val.val (-j) else 0)+
      ((t : ℂ)*(z.val.val n*conj c+c*z.val.val (-n))+(t : ℂ)^2*(c*conj c))*
        (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1).val j
  rw [WeightedCoeff.single_val]
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  by_cases hj : j=(n : ℤ)
  · subst j
    simp only [if_pos hn,physicalRealMeanZeroWeightedMode_val,Pi.single_eq_same,
      Pi.single_eq_of_ne (by omega : (n : ℤ) ≠ -(n : ℤ)),
      Pi.single_eq_of_ne (by omega : -(n : ℤ) ≠ (n : ℤ)),add_zero,zero_add,mul_one]
    ring
  · by_cases hjp : 0<j
    · have hjn : j ≠ -(n : ℤ) := by omega
      have hnj : -j ≠ (n : ℤ) := by omega
      have hnj' : -j ≠ -(n : ℤ) := by omega
      simp only [if_pos hjp,physicalRealMeanZeroWeightedMode_val,Pi.single_eq_of_ne hj,
        Pi.single_eq_of_ne hjn,Pi.single_eq_of_ne hnj,Pi.single_eq_of_ne hnj',
        add_zero,mul_zero]
    · simp only [if_neg hjp,Pi.single_eq_of_ne hj,mul_zero,add_zero]

/-- The exact weighted derivative of the complete action sequence in a
real signed mode, with no coordinatewise-to-norm gap. -/
theorem hasDerivAt_sobolevSignedActionSequence_mode_curve (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (n : ℕ+) (c : ℂ) :
    HasDerivAt (fun t : ℝ => sobolevSignedActionSequence r s hrs
      (z+t • physicalRealMeanZeroWeightedMode (Weight.sobolev s) n c))
      ((z.val.val n*conj c+c*z.val.val (-n)) •
        WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have hscalar : HasDerivAt (fun t : ℝ =>
      (t : ℂ)*(z.val.val n*conj c+c*z.val.val (-n))+(t : ℂ)^2*(c*conj c))
      (z.val.val n*conj c+c*z.val.val (-n)) 0 := by
    simpa using! (ht.mul_const _).add ((ht.pow 2).mul_const (c*conj c))
  have h := (hscalar.smul_const (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1)).const_add
    (sobolevSignedActionSequence r s hrs z)
  simpa only [←sobolevSignedActionSequence_mode_curve r s hrs z n c] using! h

end NLS
