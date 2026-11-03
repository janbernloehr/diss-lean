import NLS.ComplexAnalysis.LocalAnalyticSquareRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-! # Analytic square roots of nonvanishing functions on a disc

Lift through the exponential on the contractible disc, then use local
uniqueness of a continuous square root to recover complex analyticity.
The lift argument follows the covering-map construction in mathlib's
`Analysis.Complex.BranchLogRoot`; no principal slit assumption is made.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem analyticOnNhd_continuous_squareRoot (f h : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hh : ContinuousOn h U)
    (hne : ∀ z ∈ U, f z ≠ 0) (hsq : ∀ z ∈ U, h z^2 = f z) :
    AnalyticOnNhd ℂ h U := by
  intro z hz
  have hhz : h z ≠ 0 := by
    intro he
    exact hne z hz (by rw [← hsq z hz,he]; simp)
  obtain ⟨V,hV,hzV,r,hr,hrz,hrs⟩ :=
    exists_local_analytic_squareRoot f z (h z) (hf z hz) hhz (hsq z hz).symm
  have heq : r =ᶠ[𝓝 z] h := eventuallyEq_of_sq_eq_of_continuousAt r h z
    (hr z hzV).continuousAt (hh z hz |>.continuousAt (hU.mem_nhds hz)) hrz hhz (by
      filter_upwards [hV.mem_nhds hzV,hU.mem_nhds hz] with w hwV hwU
      exact (hrs w hwV).2.trans (hsq w hwU).symm)
  exact (hr z hzV).congr heq

/-- A nowhere-zero analytic function on a nonempty open disc has an
analytic square root on that whole disc. -/
theorem exists_analytic_squareRoot_on_ball (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball c R) ∧
      ∀ z ∈ ball c R, h z ≠ 0 ∧ h z^2 = f z := by
  classical
  let U := ball c R
  have hU : IsOpen U := isOpen_ball
  have hc : c ∈ U := mem_ball_self hR
  let _ : ContractibleSpace U := (convex_ball c R).contractibleSpace ⟨c,hc⟩
  let _ : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let x₀ : U := ⟨c,hc⟩
  obtain ⟨L,⟨_,hL⟩,_⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.domRestrict f,continuousOn_iff_continuous_domRestrict.mp hf.continuousOn⟩
    (show exp (log (f x₀)) = f x₀ from exp_log (hne x₀ x₀.2))
    (fun x => hne x x.2)
  let g : ℂ → ℂ := fun z => if hz : z ∈ U then L ⟨z,hz⟩ else 0
  have hg : ContinuousOn g U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert! L.continuous using 1
    funext z
    simp only [g,domRestrict_apply,dif_pos z.2]
  have hexp (z : ℂ) (hz : z ∈ U) : exp (g z) = f z := by
    simpa only [g,dif_pos hz,Function.comp_apply,ContinuousMap.coe_mk,domRestrict_apply]
      using congrFun hL ⟨z,hz⟩
  let h : ℂ → ℂ := fun z => exp (g z/2)
  have hh : ContinuousOn h U := (hg.div_const 2).cexp
  have hsq (z : ℂ) (hz : z ∈ U) : h z^2 = f z := by
    dsimp only [h]
    rw [← exp_nat_mul]
    convert hexp z hz using 1
    congr 1
    ring
  refine ⟨h,analyticOnNhd_continuous_squareRoot f h U hU hf hh hne hsq,?_⟩
  intro z hz
  exact ⟨exp_ne_zero _,hsq z hz⟩

end NLS.ComplexAnalysis
