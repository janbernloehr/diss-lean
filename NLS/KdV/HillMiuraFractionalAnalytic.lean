import NLS.KdV.HillMiuraFractionalLiftBound
import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.FunctionalAnalysis.LocalRealizationBound

/-! # Analytic fractional realizations of the original complex Miura lift

The target is the full strong H^(1-r) norm. The local bound proved from
the actual Miura equation supplies the analytic realization, with every
original coefficient unchanged.
-/
noncomputable section
open Set Metric Complex NLS.WeightedCoeff
namespace NLS.KdV.HillHminusMiuraChart

def fractionalLift (C : HillHminusMiuraChart) (r : ℝ) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.sobolev (1-r)) 2 :=
  ofFunctionOrZero (Weight.sobolev (1-r)) 2
    (fun k => C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) k)

theorem exists_local_fractionalLift_bound (C : HillHminusMiuraChart)
    (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ C.domain)
    (M : ℝ) (hM : 0 ≤ M) (hqM : ‖q‖ < M) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) 2), ∃ L : ℝ,
      IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ U, sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a ∈ C.domain) ∧
      ∀ a ∈ U, ∃ b : WeightedCoeff (Weight.sobolev (1-r)) 2,
        (∀ k, b.val k = C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a) k) ∧ ‖b‖ ≤ L := by
  let T : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] PeriodOneHminusOne :=
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
  obtain ⟨V,R,L,hV,hqV,hVd,_,_,hbound⟩ := C.exists_local_fractional_lift_bound (T q) hq r hr hr1 M hM
  have hb (a : WeightedCoeff (Weight.sobolev (-r)) 2) (ha : ‖a‖ ≤ M) (haV : T a ∈ V) :
      ∃ b : WeightedCoeff (Weight.sobolev (1-r)) 2,
        (∀ k, b.val k = C.lift (T a) k) ∧ ‖b‖ ≤ L := by
    obtain ⟨b,hb,_,hbL⟩ := hbound a ha haV
    exact ⟨b,hb,hbL⟩
  obtain ⟨U,hU,hqU,hUC,hUb⟩ := NLS.FunctionalAnalysis.exists_local_realization_on_ball
    T T.continuous q M hqM V hV hqV (fun a => a ∈ C.domain) hVd
    (fun (a : WeightedCoeff (Weight.sobolev (-r)) 2)
      (b : WeightedCoeff (Weight.sobolev (1-r)) 2) => ∀ k, b.val k = C.lift (T a) k) L hb
  exact ⟨U,L,hU,hqU,hUC,hUb⟩

theorem fractionalLift_analytic_and_coefficients (C : HillHminusMiuraChart)
    (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ C.domain) :
    AnalyticAt ℂ (C.fractionalLift r hr1.le) q ∧
      ∀ k, (C.fractionalLift r hr1.le q).val k =
        C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) k := by
  let T : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] PeriodOneHminusOne :=
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
  obtain ⟨U,L,hU,hqU,hUC,hb⟩ := C.exists_local_fractionalLift_bound r hr hr1 q hq
    (‖q‖+1) (by positivity) (by linarith)
  let f := fun a : WeightedCoeff (Weight.sobolev (-r)) 2 => fun k : ℤ => C.lift (T a) k
  have ha (k : ℤ) : AnalyticOnNhd ℂ (fun a => f a k) U := by
    intro a haU
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).analyticAt _).comp
      ((C.lift_analytic (T a) (hUC a haU)).comp (T.analyticAt a))
  obtain ⟨hanalytic,hdata⟩ := analytic_realization_of_bound (Weight.sobolev (1-r)) f hU ha L hb
  exact ⟨hanalytic q hqU,(hdata q hqU).2⟩

end NLS.KdV.HillHminusMiuraChart
