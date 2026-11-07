import NLS.KdV.HillNativeRealLocalInverse
import NLS.SequenceSpaces.FourierRealZeroCoordinates
import NLS.FunctionalAnalysis.LinearTargetDerivative
import NLS.ComplexAnalysis.RealAnalyticDenseNonzero

/-! Every ACTUAL positive signed coordinate is a nontrivial globally
real analytic function. Its nonzero locus is dense in the full real
mean-zero Banach source, by the verified Fourier derivative at0. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

def hillRealPositiveCoordinate (n : ℕ+) (q : HillRealMeanZeroSource) : ℂ :=
  (hillRealSignedMap q).val.val.val (n:ℤ)

theorem analyticAt_hillRealPositiveCoordinate (n : ℕ+) (q : HillRealMeanZeroSource) :
    AnalyticAt ℝ (hillRealPositiveCoordinate n) q := by
  have hL : AnalyticAt ℝ
      (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 (n:ℤ))
      (hillRealSignedMap q) := _root_.ContinuousLinearMap.analyticAt _ _
  exact hL.comp (f := hillRealSignedMap) (analyticAt_hillRealSignedMap q)

theorem fderiv_hillRealPositiveCoordinate_zero_apply (n : ℕ+) (h : HillRealMeanZeroSource) :
    (fderiv ℝ (hillRealPositiveCoordinate n) 0) h=
      WeightedCoeff.halfFourierSymbol (n:ℤ)*h.val.val.val (n:ℤ) := by
  have hd := @NLS.FunctionalAnalysis.fderiv_comp_clm_apply ℝ HillRealMeanZeroSource HillRealSignedTarget ℂ
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hillRealSignedMap
    (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 (n:ℤ)) 0 h
    (analyticAt_hillRealSignedMap 0).differentiableAt
  change (fderiv ℝ (hillRealPositiveCoordinate n) 0) h=
    ((fderiv ℝ hillRealSignedMap 0) h).val.val.val (n:ℤ) at hd
  rw [hd,fderiv_hillRealSignedMap_zero_apply]

theorem fderiv_hillRealPositiveCoordinate_cosine_ne_zero (n : ℕ+) :
    (fderiv ℝ (hillRealPositiveCoordinate n) 0)
      (WeightedCoeff.realCosineDirection (p := 2) (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) n) ≠ 0 := by
  rw [fderiv_hillRealPositiveCoordinate_zero_apply,WeightedCoeff.realCosineDirection_positive,mul_one]
  exact WeightedCoeff.halfFourierSymbol_ne_zero _

theorem exists_hillRealPositiveCoordinate_ne_zero (n : ℕ+) :
    ∃ q : HillRealMeanZeroSource, hillRealPositiveCoordinate n q ≠ 0 := by
  by_contra hz
  have hzero : hillRealPositiveCoordinate n=(fun _ : HillRealMeanZeroSource => (0:ℂ)) := by
    funext q
    by_contra hq
    exact hz ⟨q,hq⟩
  have hd := fderiv_hillRealPositiveCoordinate_cosine_ne_zero n
  rw [hzero,fderiv_const_apply,zero_apply] at hd
  exact hd rfl

theorem dense_hillRealPositiveCoordinate_ne_zero (n : ℕ+) :
    Dense {q : HillRealMeanZeroSource | hillRealPositiveCoordinate n q ≠ 0} := by
  obtain ⟨a,ha⟩ := exists_hillRealPositiveCoordinate_ne_zero n
  exact @NLS.ComplexAnalysis.dense_ne_zero_of_real_analytic HillRealMeanZeroSource ℂ
    inferInstance inferInstance inferInstance inferInstance _
    (fun q _ => analyticAt_hillRealPositiveCoordinate n q) a ha

end NLS.KdV
