import NLS.SequenceSpaces.HolderEmbedding

/-! # A strict Hilbert embedding at every finite Fourier-Lebesgue exponent above two

The loss is 1/2-1/(2p), strictly smaller than one half. The positive
margin 1/(2p) is retained for the endpoint Miura regularity argument.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS

def fourierLebesgueHilbertHolderExponent (p : ℝ) : ℝ := (1/2-1/p)⁻¹

theorem fourierLebesgueHilbertHolderExponent_pos (p : ℝ) (hp : 2<p) :
    0<fourierLebesgueHilbertHolderExponent p := by
  apply inv_pos.mpr
  have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<2) hp
  linarith

theorem one_le_fourierLebesgueHilbertHolderExponent (p : ℝ) (hp : 2<p) :
    1≤fourierLebesgueHilbertHolderExponent p := by
  have hd : 0<1/2-1/p := inv_pos.mp (fourierLebesgueHilbertHolderExponent_pos p hp)
  rw [fourierLebesgueHilbertHolderExponent,one_le_inv₀ hd]
  have hpi : 0<1/p := by positivity
  linarith

theorem holderTriple_fourierLebesgueHilbert (p : ℝ) (hp : 2<p) :
    (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal (fourierLebesgueHilbertHolderExponent p)) 2 := by
  rw [ENNReal.holderTriple_iff]
  rw [show (2 : ℝ≥0∞)=ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [←ENNReal.ofReal_inv_of_pos (by linarith : 0<p),
    ←ENNReal.ofReal_inv_of_pos (fourierLebesgueHilbertHolderExponent_pos p hp),
    ←ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),
    ←ENNReal.ofReal_add (by positivity : (0:ℝ)≤p⁻¹)
      (inv_nonneg.mpr (fourierLebesgueHilbertHolderExponent_pos p hp).le)]
  congr 1
  simp only [fourierLebesgueHilbertHolderExponent,inv_inv,one_div]
  ring

theorem fourierLebesgueHilbert_loss_threshold (p : ℝ) (hp : 2<p) :
    1<(1/2-1/(2*p))*fourierLebesgueHilbertHolderExponent p := by
  have hd : 0<1/2-1/p := inv_pos.mp (fourierLebesgueHilbertHolderExponent_pos p hp)
  rw [fourierLebesgueHilbertHolderExponent,←div_eq_mul_inv,one_lt_div hd]
  have hpi : 0<p := by linarith
  have h : 1/(2*p)<1/p := one_div_lt_one_div_of_lt hpi (by linarith)
  linarith

namespace WeightedCoeff

/-- An identity on raw coefficients in the exact original weighted norms. -/
def fourierLebesgueHilbertInclusion (s p : ℝ) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)] :
    WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →L[ℂ]
      WeightedCoeff (Weight.sobolev (s-1/2+1/(2*p))) 2 := by
  let r := ENNReal.ofReal (fourierLebesgueHilbertHolderExponent p)
  letI : Fact (1≤r) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_fourierLebesgueHilbertHolderExponent p hp)⟩
  letI : (ENNReal.ofReal p).HolderTriple r 2 := holderTriple_fourierLebesgueHilbert p hp
  apply sobolevHolderInclusion (r := r) s (s-1/2+1/(2*p)) ENNReal.ofReal_ne_top
  simpa only [r,ENNReal.toReal_ofReal (fourierLebesgueHilbertHolderExponent_pos p hp).le,
    show s-(s-1/2+1/(2*p))=1/2-1/(2*p) by ring] using fourierLebesgueHilbert_loss_threshold p hp

@[simp] theorem fourierLebesgueHilbertInclusion_apply (s p : ℝ) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) (n : ℤ) :
    (fourierLebesgueHilbertInclusion s p hp a).val n=a.val n := by
  let r := ENNReal.ofReal (fourierLebesgueHilbertHolderExponent p)
  let : Fact (1≤r) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_fourierLebesgueHilbertHolderExponent p hp)⟩
  let : (ENNReal.ofReal p).HolderTriple r 2 := holderTriple_fourierLebesgueHilbert p hp
  have ht : 1<(s-(s-1/2+1/(2*p)))*r.toReal := by
    simpa only [r,ENNReal.toReal_ofReal (fourierLebesgueHilbertHolderExponent_pos p hp).le,
      show s-(s-1/2+1/(2*p))=1/2-1/(2*p) by ring] using fourierLebesgueHilbert_loss_threshold p hp
  exact sobolevHolderInclusion_apply (r := r) s (s-1/2+1/(2*p)) ENNReal.ofReal_ne_top ht a n

theorem memlp_hilbert_of_fourierLebesgue (s p : ℝ) (hp : 2<p) {a : ℤ → ℂ}
    (ha : Memℓp (fun n => (Weight.sobolev s n : ℂ)*a n) (ENNReal.ofReal p)) :
    Memℓp (fun n => (Weight.sobolev (s-1/2+1/(2*p)) n : ℂ)*a n) 2 := by
  let : Fact (1≤ENNReal.ofReal p) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1:ℝ)≤p by linarith)⟩
  let b : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) := ⟨a,ha⟩
  have h := (fourierLebesgueHilbertInclusion s p hp b).property
  change Memℓp (fun n => (Weight.sobolev (s-1/2+1/(2*p)) n : ℂ)*
    (fourierLebesgueHilbertInclusion s p hp b).val n) 2 at h
  have he : (fun n => (Weight.sobolev (s-1/2+1/(2*p)) n : ℂ)*
      (fourierLebesgueHilbertInclusion s p hp b).val n) =
      (fun n => (Weight.sobolev (s-1/2+1/(2*p)) n : ℂ)*a n) := by
    funext n
    exact congrArg (fun z : ℂ => (Weight.sobolev (s-1/2+1/(2*p)) n : ℂ)*z)
      (fourierLebesgueHilbertInclusion_apply s p hp b n)
  rw [he] at h
  exact h

end WeightedCoeff
end NLS
