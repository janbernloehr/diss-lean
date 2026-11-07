import NLS.KdV.HillRoughFourierLebesguePositiveGerms
import NLS.KdV.HillRoughFourierLebesgueInverseCompatibility
import NLS.SequenceSpaces.PhysicalPositiveCompletionExponent

/-! # Native real analyticity of the fixed physical Fourier-Lebesgue map

Weighted analytic Dirac germs, the actual retained chart and the exact
physical sign choices recover the SAME global map on the real slice.
The bounded real-linear signed completion uses the ORIGINAL target norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

private theorem physical_signed_weight_conversion (s : ℝ) (j : ℤ) (z : ℂ) :
    (Weight.sobolev (s+1) j : ℂ)*z/(Weight.sobolev (s+1/2) j : ℂ)=
      z/(Weight.sobolev (-1/2) j : ℂ) := by
  have hw : (Weight.sobolev (s+1) j : ℂ)*(Weight.sobolev (-1/2) j : ℂ)=
      (Weight.sobolev (s+1/2) j : ℂ) := by
    rw [←ofReal_mul,←Weight.sobolev_add,show s+1+(-1/2)=s+1/2 by ring]
  apply (div_eq_div_iff (Weight.complex_ne_zero _ _) (Weight.complex_ne_zero _ _)).mpr
  rw [mul_assoc,mul_comm z,←mul_assoc,hw,mul_comm]

/-- Native REAL analyticity of the SAME physical restriction for every
finite real p>2, with both exact original native norms. -/
theorem fourierLebesgueForward_analytic_of_two_lt (D : GlobalRoughAbelianForwardData)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)] :
    AnalyticOnNhd ℝ (D.fourierLebesgueForward s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top
      (by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le)) univ := by
  let hp2 : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  let L := periodOneFourierLebesgueImageInclusion s p hs hp
  have hL (b : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) :
      fourierLebesgueSourceInclusion s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp2 b=L b := by
    apply Subtype.ext
    funext j
    simp only [fourierLebesgueSourceInclusion_apply,L,periodOneFourierLebesgueImageInclusion_apply]
  have hreal (b : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) (ENNReal.ofReal p)) :
      IsRealPeriodOneHminusOne (L b.val) := by
    intro j
    simpa only [L,periodOneFourierLebesgueImageInclusion_apply] using b.property.1 j
  intro a _
  let q0 : PeriodOneRealHminusOne := ⟨L a.val,hreal a⟩
  let R := D.chart q0
  have haB : L a.val∈ball q0.val R.data.radius := mem_ball_self R.data.radius_pos
  obtain ⟨V,hV,haV,C,G,_hC,hGa,hd⟩ := R.exists_fourierLebesgue_positive_germ s p hs hp a.val haB (hreal a)
  let J := (physicalRealMeanZeroWeightedExponent (Weight.sobolev s) (ENNReal.ofReal p)).subtypeL
  let A := WeightedCoeff.physicalPositiveRealLift (Weight.sobolev (s+1/2)) (ENNReal.ofReal p)
    (Weight.sobolev_neg (s+1/2))
  have hanalytic := NLS.ComplexAnalysis.analytic_real_linear_germ_transport J A G a (hGa a.val haV)
  apply hanalytic.congr
  filter_upwards [(hV.preimage continuous_subtype_val).mem_nhds haV] with b hb
  have hbD := hd b.val hb
  have hpositive (j : ℤ) (hj : 0<j) :
      (A (G b.val)).val.val j=
        (D.fourierLebesgueForward s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp2 b).val.val j := by
    rw [D.fourierLebesgueForward_apply,hL]
    change (WeightedCoeff.physicalPositiveRealLift _ _ _ (G b.val)).val.val j=(D.signed (L b.val)).val j
    rw [WeightedCoeff.physicalPositiveRealLift_apply,if_pos hj,
      if_neg (by omega : ¬0< -j),map_zero,add_zero,(hbD.2.2.2 (hreal b)) j]
    have hglob := D.positive_local q0 hbD.1
    rw [←hglob,D.signed_positive_real (L b.val) (hreal b) j hj]
    exact physical_signed_weight_conversion s j (D.positive (L b.val) j)
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hj : 0<j
  · exact hpositive j hj
  · by_cases hzero : j=0
    · subst j
      exact (A (G b.val)).property.2.trans
        (D.fourierLebesgueForward s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp2 b).property.2.symm
    · calc
        (A (G b.val)).val.val j=conj ((A (G b.val)).val.val (-j)) := by
          simpa only [neg_neg] using (A (G b.val)).property.1 (-j)
        _ = conj ((D.fourierLebesgueForward s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp2 b).val.val (-j)) :=
          congrArg conj (hpositive (-j) (by omega))
        _ = (D.fourierLebesgueForward s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp2 b).val.val j := by
          simpa only [neg_neg] using
            ((D.fourierLebesgueForward s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp2 b).property.1 (-j)).symm

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
