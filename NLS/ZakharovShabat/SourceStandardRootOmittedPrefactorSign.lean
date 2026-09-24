import NLS.ZakharovShabat.SourceStandardRootOmittedPairSigns

/-!
# Sign of the zero-mode prefactor in an omitted-root product

For every nonzero selected gap, the zero root and the selected
normalizing denominator have opposite signs. This supplies the
additional negative sign in the parity count.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a noncentral real gap, the zero-mode prefactor of the omitted
standard-root product is strictly negative. -/
theorem sourceStandardRootOmittedPrefactor_re_neg_on_nonzeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {n : ℤ} (hn : n ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (((if n = 0 then 1 else sourceStandardRoot hp hp1 ψ 0 (x:ℂ)) /
      singleSpectralDenominator n)).re < 0 := by
  have hroot : (sourceStandardRoot hp hp1 ψ 0 (x:ℂ)).im = 0 :=
    sourceStandardRoot_im_eq_zero_off_selected_realGap
      hp hp1 ψ hreal (Ne.symm hn) hx
  have hden : (singleSpectralDenominator n).im = 0 := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hquot : (sourceStandardRoot hp hp1 ψ 0 (x:ℂ) /
      singleSpectralDenominator n).re =
      (sourceStandardRoot hp hp1 ψ 0 (x:ℂ)).re /
        (singleSpectralDenominator n).re := by
    let w := sourceStandardRoot hp hp1 ψ 0 (x:ℂ)
    let d := singleSpectralDenominator n
    have hw : w = (w.re:ℂ) := by
      apply Complex.ext
      · rfl
      · exact hroot
    have hd : d = (d.re:ℂ) := by
      apply Complex.ext
      · rfl
      · exact hden
    change (w/d).re = w.re/d.re
    rw [hw,hd]
    simp
  simp only [if_neg hn]
  rw [hquot]
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · exact div_neg_of_pos_of_neg
      (sourceStandardRoot_re_pos_after_realGap hp hp1 ψ hreal hnneg hx)
      (singleSpectralDenominator_re_neg_of_neg n hnneg)
  · exact div_neg_of_neg_of_pos
      (sourceStandardRoot_re_neg_before_realGap hp hp1 ψ hreal hnpos hx)
      (singleSpectralDenominator_re_pos_of_nonneg n hnpos.le)

end NLS.ZakharovShabat
