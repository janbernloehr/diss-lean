import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Analyticity along limits of directions

For a norm-continuous map on an open set, analyticity along convergent
directions passes to the limiting direction. Joint continuity gives
uniform convergence on a compact scalar disc; the holomorphic limit
theorem then supplies analyticity in the target Banach norm.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Continuity of a family gives uniform convergence on a compact parameter
set when its external parameter converges within the family domain. -/
theorem tendstoUniformlyOn_continuous_family (f : E → ℂ → F) (S : Set E) (K : Set ℂ)
    (hK : IsCompact K) (hf : ContinuousOn f.uncurry (S ×ˢ K))
    (d : E) (hd : d ∈ S) (v : ι → E) (l : Filter ι) (hv : Tendsto v l (𝓝[S] d)) :
    TendstoUniformlyOn (fun i => f (v i)) (f d) l K := by
  intro u hu
  obtain ⟨B,hB,hbound⟩ := hK.mem_uniformity_of_prod hf hd (symm_le_uniformity hu)
  filter_upwards [hv.eventually hB] with i hi t ht
  exact hbound (v i) hi t ht

/-- A limit of directions with analytic affine slices is again an analytic
direction, assuming only continuity of the original map on its open domain. -/
theorem analyticAt_line_of_tendsto_directions
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (a : E) (ha : a ∈ U) (d : E) (v : ι → E) (l : Filter ι) [l.NeBot]
    (hv : Tendsto v l (𝓝 d))
    (han : ∀ᶠ i in l, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v i))
      ((fun t : ℂ => a+t • v i) ⁻¹' U)) :
    AnalyticAt ℂ (fun t : ℂ => f (a+t • d)) 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU a ha
  let R : ℝ := ε/(2*(‖d‖+1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hRmul : R*(‖d‖+1) = ε/2 := by dsimp [R]; field_simp
  have hinto (w : E) (hw : w ∈ ball d 1) (t : ℂ) (ht : t ∈ closedBall 0 R) : a+t • w ∈ U := by
    apply hball
    have hw' : ‖w-d‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hw
    have hwn : ‖w‖ ≤ ‖d‖+1 := by linarith [norm_le_norm_sub_add w d]
    have htn : ‖t‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using ht
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul]
    calc
      ‖t‖*‖w‖ ≤ R*(‖d‖+1) := mul_le_mul htn hwn (norm_nonneg _) hR.le
      _ = ε/2 := hRmul
      _ < ε := by linarith
  have hjoint : ContinuousOn (fun x : E × ℂ => f (a+x.2 • x.1))
      (ball d 1 ×ˢ closedBall 0 R) :=
    hf.comp (continuous_const.add (continuous_snd.smul continuous_fst)).continuousOn
      (fun x hx => hinto x.1 hx.1 x.2 hx.2)
  have hve : ∀ᶠ i in l, v i ∈ ball d 1 := hv.eventually (ball_mem_nhds d (by norm_num))
  have hwithin : Tendsto v l (𝓝[ball d 1] d) := tendsto_nhdsWithin_iff.mpr ⟨hv,hve⟩
  have hunif := tendstoUniformlyOn_continuous_family (fun w t => f (a+t • w))
    (ball d 1) (closedBall 0 R) (isCompact_closedBall _ _) hjoint d
    (mem_ball_self (by norm_num)) v l hwithin
  have hdiff : ∀ᶠ i in l, DifferentiableOn ℂ (fun t : ℂ => f (a+t • v i)) (ball 0 R) := by
    filter_upwards [han,hve] with i hi hvi
    exact (hi.mono (fun t ht => hinto (v i) hvi t (ball_subset_closedBall ht))).differentiableOn
  exact ((hunif.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn hdiff
    isOpen_ball).analyticAt (ball_mem_nhds 0 hR)

/-- The limiting line is analytic on its entire open preimage, not just
at the original center. -/
theorem analyticOnNhd_line_of_tendsto_directions
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (d : E) (v : ι → E) (l : Filter ι) [l.NeBot] (hv : Tendsto v l (𝓝 d))
    (han : ∀ a ∈ U, ∀ᶠ i in l, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v i))
      ((fun t : ℂ => a+t • v i) ⁻¹' U)) (a : E) :
    AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • d)) ((fun t : ℂ => a+t • d) ⁻¹' U) := by
  intro t ht
  have hzero := analyticAt_line_of_tendsto_directions f U hU hf (a+t • d) ht d v l hv
    (han (a+t • d) ht)
  have hh : AnalyticAt ℂ (fun u : ℂ => f (a+t • d+u • d)) (t-t) := by
    simpa only [sub_self] using hzero
  have hshift : AnalyticAt ℂ (fun u : ℂ => u-t) t := analyticAt_id.sub analyticAt_const
  have he (u : ℂ) : a+t • d+(u-t) • d = a+u • d := by rw [sub_smul]; abel
  simpa only [Function.comp_def,he] using hh.comp (f := fun u : ℂ => u-t) hshift

end NLS.ComplexAnalysis
