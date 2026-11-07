import NLS.SequenceSpaces.FourierLebesgueHilbertEmbedding

/-! # Coefficient-preserving Hilbert inclusions at every finite exponent p>=2 -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.WeightedCoeff

def finiteFourierLebesgueWeakInclusion (s t : ℝ) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p)
    [Fact (1≤p)] (hst : t≤s-1/2+1/(2*p.toReal)) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.sobolev t) 2 := by
  by_cases he : p=2
  · subst p
    exact sobolevInclusion (hst.trans (by norm_num;linarith : s-1/2+1/(2*(2 : ℝ≥0∞).toReal)≤s))
  · have hpR : 2<p.toReal := by
      have hlt : (2 : ℝ≥0∞)<p := lt_of_le_of_ne h2p (Ne.symm he)
      simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal (by norm_num) hp).mpr hlt
    let r := ENNReal.ofReal (fourierLebesgueHilbertHolderExponent p.toReal)
    letI : Fact (1≤r) := ⟨by
      exact_mod_cast ENNReal.ofReal_le_ofReal
        (one_le_fourierLebesgueHilbertHolderExponent p.toReal hpR)⟩
    letI : p.HolderTriple r 2 := by
      have h := holderTriple_fourierLebesgueHilbert p.toReal hpR
      simpa only [ENNReal.ofReal_toReal hp] using h
    apply sobolevHolderInclusion (r := r) s t ENNReal.ofReal_ne_top
    have hr : 0<fourierLebesgueHilbertHolderExponent p.toReal :=
      fourierLebesgueHilbertHolderExponent_pos p.toReal hpR
    have hbase := fourierLebesgueHilbert_loss_threshold p.toReal hpR
    simp only [r,ENNReal.toReal_ofReal hr.le]
    nlinarith

@[simp] theorem finiteFourierLebesgueWeakInclusion_apply
    (s t : ℝ) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (hst : t≤s-1/2+1/(2*p.toReal)) (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (finiteFourierLebesgueWeakInclusion s t p hp h2p hst a).val n=a.val n := by
  unfold finiteFourierLebesgueWeakInclusion
  split
  next he =>
    subst p
    exact sobolevInclusion_apply _ _ _
  next he =>
    have hpR : 2<p.toReal := by
      have hlt : (2 : ℝ≥0∞)<p := lt_of_le_of_ne h2p (Ne.symm he)
      simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal (by norm_num) hp).mpr hlt
    let r := ENNReal.ofReal (fourierLebesgueHilbertHolderExponent p.toReal)
    let : Fact (1≤r) := ⟨by
      exact_mod_cast ENNReal.ofReal_le_ofReal
        (one_le_fourierLebesgueHilbertHolderExponent p.toReal hpR)⟩
    let : p.HolderTriple r 2 := by
      have h := holderTriple_fourierLebesgueHilbert p.toReal hpR
      simpa only [ENNReal.ofReal_toReal hp] using h
    exact sobolevHolderInclusion_apply (r := r) s t ENNReal.ofReal_ne_top _ a n

theorem finiteFourierLebesgueWeakInclusion_injective
    (s t : ℝ) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (hst : t≤s-1/2+1/(2*p.toReal)) :
    Function.Injective (finiteFourierLebesgueWeakInclusion s t p hp h2p hst) := by
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [finiteFourierLebesgueWeakInclusion_apply] using
    congrArg (fun q => q.val n) hab

end NLS.WeightedCoeff
