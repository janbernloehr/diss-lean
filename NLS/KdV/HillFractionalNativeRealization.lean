import NLS.KdV.HillFractionalNativeMap
import NLS.SequenceSpaces.SignedSobolevNegativeEquivalence

/-! One canonical strong fractional realization of the actual native
map, analytic near every real source. The definition does not select a chart. -/
noncomputable section
open Set Filter Topology NLS.WeightedCoeff
namespace NLS.KdV

def hillFractionalNativeRealization (r : ℝ) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.signedSobolev (1/2-r)) 2 :=
  ofFunctionOrZero _ 2 (hillHminusNativeComplexMap
    (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).val

theorem hillFractionalNativeRealization_local (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    AnalyticAt ℂ (hillFractionalNativeRealization r hr1) q ∧
      ∀ᶠ a in 𝓝 q, ∀ k, (hillFractionalNativeRealization r hr1 a).val k =
        (hillHminusNativeComplexMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a)).val k := by
  obtain ⟨F,U,hU,hqU,hF,hraw⟩ := exists_hillFractionalNativeMap_analytic r hr hr1 q hq
  have he : hillFractionalNativeRealization r hr1 =ᶠ[𝓝 q] F := by
    filter_upwards [hU.mem_nhds hqU] with a ha
    exact ofFunctionOrZero_eq_of_coordinates _ _ (F a) (hraw a ha)
  exact ⟨(hF q hqU).congr he.symm, by
    filter_upwards [hU.mem_nhds hqU,he] with a ha heq
    rw [heq]
    exact hraw a ha⟩

theorem hillFractionalNativeRealization_apply (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) (k : ℤ) :
    (hillFractionalNativeRealization r hr1 q).val k =
      (hillHminusNativeComplexMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).val k :=
  (hillFractionalNativeRealization_local r hr hr1 q hq).2.self_of_nhds k

def hillFractionalFourierDefect (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.signedSobolev (1/2-r)) 2 :=
  hillFractionalNativeRealization r hr1 q-negativeSobolevHalfFourierEquiv r hr q

theorem analyticAt_hillFractionalFourierDefect (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    AnalyticAt ℂ (hillFractionalFourierDefect r hr hr1) q :=
  (hillFractionalNativeRealization_local r hr hr1 q hq).1.sub
    ((negativeSobolevHalfFourierEquiv r hr).analyticAt q)

end NLS.KdV
