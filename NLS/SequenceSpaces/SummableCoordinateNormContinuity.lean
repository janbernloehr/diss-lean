import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.SequenceSpaces



variable {ι X : Type*} [TopologicalSpace X]

theorem continuousAt_lp_one_of_coordinatewise_of_norm
    (f : X → lp (fun _ : ι => ℂ) 1) (x : X)
    (hc : ∀ i, ContinuousAt (fun y => f y i) x)
    (hn : ContinuousAt (fun y => ‖f y‖) x) : ContinuousAt f x := by
  let head (s : Finset ι) (y : X) : lp (fun _ : ι => ℂ) 1 :=
    ∑ i ∈ s, lp.single 1 i (f y i)
  have hhead (s : Finset ι) : ContinuousAt (head s) x := by
    apply tendsto_finsetSum
    intro i _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 1 i).continuous.continuousAt.comp
      (hc i)
  have htail (s : Finset ι) : ContinuousAt (fun y => ‖f y-head s y‖) x := by
    have hs : ContinuousAt (fun y => ‖f y‖-∑ i ∈ s, ‖f y i‖) x :=
      hn.sub (tendsto_finsetSum _ (fun i _ => (hc i).norm))
    have he (y : X) : ‖f y-head s y‖=‖f y‖-∑ i ∈ s, ‖f y i‖ := by
      simpa only [ENNReal.toReal_one,Real.rpow_one] using
        lp.norm_compl_sum_single (by norm_num : 0 < (1:ℝ≥0∞).toReal) (f y) s
    simpa only [←he] using hs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,hs⟩ := ((lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (f x)).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε/4))).exists
  have hs' : ‖f x-head s x‖ < ε/4 := by
    simpa only [mem_ball,dist_eq_norm,norm_sub_rev,head] using hs
  have ht : ∀ᶠ y in 𝓝 x, ‖f y-head s y‖ < ε/3 :=
    (htail s).eventually (gt_mem_nhds (by linarith : ‖f x-head s x‖ < ε/3))
  have hh : ∀ᶠ y in 𝓝 x, dist (head s y) (head s x) < ε/3 :=
    (hhead s).eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε/3))
  filter_upwards [ht,hh] with y hy hh
  rw [dist_eq_norm] at hh ⊢
  have he : f y-f x = (f y-head s y)+(head s y-head s x)+(head s x-f x) := by abel
  rw [he]
  have h₁ := norm_add_le ((f y-head s y)+(head s y-head s x)) (head s x-f x)
  have h₂ := norm_add_le (f y-head s y) (head s y-head s x)
  rw [norm_sub_rev (head s x)] at h₁
  linarith

end NLS.SequenceSpaces
