import NLS.ComplexAnalysis.AnalyticLineLimit
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! # Continuous directional derivatives of analytic line restrictions

For a continuous map whose complex affine slices are analytic, the line
derivative varies continuously with both center and direction. No joint
Fréchet differentiability is assumed in this result.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Every line derivative exists at every point of the open domain. -/
theorem hasLineDerivAt_of_analyticLines
    (f : E → F) (U : Set E)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a : E) (ha : a ∈ U) (v : E) :
    HasLineDerivAt ℂ f (lineDeriv ℂ f a v) a v :=
  (hl a ha v 0 (by simpa using ha)).differentiableAt.hasDerivAt

/-- Line derivatives depend jointly continuously on the center and direction. -/
theorem continuousAt_lineDeriv_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a v : E) (ha : a ∈ U) :
    ContinuousAt (fun p : E × E => lineDeriv ℂ f p.1 p.2) (a,v) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU a ha
  let S : Set (E × E) := ball a (ε/4) ×ˢ ball v 1
  let R : ℝ := ε/(4*(‖v‖+1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hRmul : R*(‖v‖+1) = ε/4 := by dsimp [R]; field_simp
  have hS : IsOpen S := isOpen_ball.prod isOpen_ball
  have hpS : (a,v) ∈ S := ⟨mem_ball_self (by positivity),mem_ball_self (by norm_num)⟩
  have hinto (p : E × E) (hp : p ∈ S) (t : ℂ) (ht : t ∈ closedBall 0 R) : p.1+t • p.2 ∈ U := by
    apply hball
    have hp1 : ‖p.1-a‖ < ε/4 := by simpa only [mem_ball,dist_eq_norm] using hp.1
    have hp2 : ‖p.2-v‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hp.2
    have hvn : ‖p.2‖ ≤ ‖v‖+1 := by linarith [norm_le_norm_sub_add p.2 v]
    have htn : ‖t‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using ht
    have hprod : ‖t‖*‖p.2‖ ≤ ε/4 := (mul_le_mul htn hvn (norm_nonneg _) hR.le).trans_eq hRmul
    rw [mem_ball,dist_eq_norm]
    calc
      ‖p.1+t • p.2-a‖ = ‖(p.1-a)+t • p.2‖ := by congr 1; abel
      _ ≤ ‖p.1-a‖+‖t‖*‖p.2‖ := by simpa only [norm_smul] using norm_add_le (p.1-a) (t • p.2)
      _ < ε := by linarith
  have hj : ContinuousOn (fun x : (E × E) × ℂ => f (x.1.1+x.2 • x.1.2))
      (S ×ˢ closedBall 0 R) :=
    hf.comp (continuous_fst.fst.add (continuous_snd.smul continuous_fst.snd)).continuousOn
      (fun x hx => hinto x.1 hx.1 x.2 hx.2)
  have hwithin : Tendsto (fun p : E × E => p) (𝓝 (a,v)) (𝓝[S] (a,v)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id,hS.mem_nhds hpS⟩
  have hu := tendstoUniformlyOn_continuous_family (fun (p : E × E) (t : ℂ) => f (p.1+t • p.2)) S
    (closedBall 0 R) (isCompact_closedBall _ _) hj (a,v) hpS (fun p => p) (𝓝 (a,v)) hwithin
  have hd : ∀ᶠ p : E × E in 𝓝 (a,v), DifferentiableOn ℂ (fun t : ℂ => f (p.1+t • p.2))
      (ball 0 R) := by
    filter_upwards [hS.mem_nhds hpS] with p hp
    have hp1 : p.1 ∈ U := by simpa using hinto p hp 0 (mem_closedBall_self hR.le)
    exact ((hl p.1 hp1 p.2).mono (fun t ht => hinto p hp t (ball_subset_closedBall ht))).differentiableOn
  exact (((hu.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.deriv hd isOpen_ball).tendsto_at
    (mem_ball_self hR) : Tendsto (fun p : E × E => lineDeriv ℂ f p.1 p.2) (𝓝 (a,v))
      (𝓝 (lineDeriv ℂ f a v)))

/-- Joint continuity on the full center-direction domain. -/
theorem continuousOn_lineDeriv_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) :
    ContinuousOn (fun p : E × E => lineDeriv ℂ f p.1 p.2) (U ×ˢ univ) :=
  fun p hp => (continuousAt_lineDeriv_of_analyticLines f U hU hf hl p.1 p.2 hp.1).continuousWithinAt

end NLS.ComplexAnalysis
