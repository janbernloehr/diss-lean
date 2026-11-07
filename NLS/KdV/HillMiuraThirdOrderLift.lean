import NLS.KdV.HillMiuraFractionalAnalytic

/-! One fixed third-order Miura lift for the entire range r <= 2/3. -/
noncomputable section
open Complex NLS.WeightedCoeff
namespace NLS.KdV.HillHminusMiuraChart

def thirdOrderLift (C : HillHminusMiuraChart) (r : ℝ) (hr : r ≤ 2/3)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.sobolev (1/3)) 2 :=
  sobolevInclusion (show (1/3:ℝ) ≤ 1-(2/3:ℝ) by norm_num)
    (C.fractionalLift (2/3) (by norm_num)
      (sobolevInclusion (show -(2/3:ℝ) ≤ -r by linarith) q))

theorem thirdOrderLift_analytic_and_coefficients (C : HillHminusMiuraChart)
    (r : ℝ) (hr : r ≤ 2/3) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ C.domain) :
    AnalyticAt ℂ (C.thirdOrderLift r hr) q ∧
      ∀ k, (C.thirdOrderLift r hr q).val k =
        C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) k := by
  let J : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-(2/3:ℝ))) 2 :=
    sobolevInclusion (show -(2/3:ℝ) ≤ -r by linarith)
  have heq : sobolevInclusion (show (-1:ℝ) ≤ -(2/3:ℝ) by norm_num) (J q) =
      sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q := by
    apply Subtype.ext
    funext k
    simp only [sobolevInclusion_apply,J]
  have hq' : sobolevInclusion (show (-1:ℝ) ≤ -(2/3:ℝ) by norm_num) (J q) ∈ C.domain := by
    rw [heq]
    exact hq
  obtain ⟨ha,hc⟩ := C.fractionalLift_analytic_and_coefficients (2/3) (by norm_num) (by norm_num) (J q) hq'
  let K : WeightedCoeff (Weight.sobolev (1-(2/3:ℝ))) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (1/3)) 2 :=
    sobolevInclusion (by norm_num)
  have hcomp := (K.analyticAt _).comp (ha.comp (J.analyticAt q))
  refine ⟨hcomp,?_⟩
  intro k
  change (sobolevInclusion _ (C.fractionalLift (2/3) _ (J q))).val k = _
  rw [sobolevInclusion_apply,hc,heq]

end NLS.KdV.HillHminusMiuraChart
