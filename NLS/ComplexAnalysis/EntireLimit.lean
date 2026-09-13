import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Entire limits across countable exceptional sets

The maximum modulus principle transfers uniform Cauchy estimates from a
circle to its closed disc. Circles avoiding a countable exceptional set then
upgrade locally uniform convergence off that set to locally uniform convergence
on the whole plane, with a unique entire limit.
-/

noncomputable section
open Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- Uniform Cauchy bounds on a circle propagate to its disc for entire functions. -/
theorem uniformCauchySeqOn_closedBall_of_sphere (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, Differentiable ℂ (F n)) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (h : UniformCauchySeqOn F atTop (sphere c r)) :
    UniformCauchySeqOn F atTop (closedBall c r) := by
  rw [Metric.uniformCauchySeqOn_iff] at h ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := h (ε/2) (half_pos hε)
  refine ⟨N,fun m hm n hn z hz => ?_⟩
  have hb : ‖F m z-F n z‖ ≤ ε/2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((hF m).sub (hF n)).diffContOnCl
    · intro w hw
      rw [frontier_ball c (ne_of_gt hr)] at hw
      exact (show ‖F m w-F n w‖ < ε/2 from by
        simpa only [dist_eq_norm] using hN m hm n hn w hw).le
    · simpa only [closure_ball c (ne_of_gt hr)] using hz
  rw [dist_eq_norm]
  exact hb.trans_lt (half_lt_self hε)

/-- Arbitrarily large circles centered at zero avoid a countable set. -/
theorem exists_sphere_subset_compl_countable (S : Set ℂ) (hS : S.Countable) (R : ℝ) :
    ∃ r : ℝ, R < r ∧ sphere (0 : ℂ) r ⊆ Sᶜ := by
  obtain ⟨r,hr,hR⟩ := ((hS.image (fun z : ℂ => ‖z‖)).dense_compl ℝ).exists_mem_open
    isOpen_Ioi (Set.nonempty_Ioi : (Set.Ioi R).Nonempty)
  refine ⟨r,hR,?_⟩
  intro z hz hzs
  apply hr
  exact ⟨z,hzs,by simpa only [mem_sphere, dist_zero_right] using hz⟩

/-- The pointwise limit of a sequence, used only under proved convergence hypotheses. -/
def entireSequenceLimit (F : ℕ → ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder atTop (fun n => F n z)

/-- Off-exceptional locally uniform convergence yields uniformly Cauchy closed discs of every size. -/
theorem exists_large_uniformCauchySeqOn_closedBall (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, Differentiable ℂ (F n)) (S : Set ℂ) (hS : S.Countable) (g : ℂ → ℂ)
    (h : TendstoLocallyUniformlyOn F g atTop Sᶜ) (R : ℝ) :
    ∃ r : ℝ, max R 0 < r ∧ UniformCauchySeqOn F atTop (closedBall (0 : ℂ) r) := by
  obtain ⟨r,hr,hs⟩ := exists_sphere_subset_compl_countable S hS (max R 0)
  have hc := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere 0 r)).mp
    (h.mono hs)
  exact ⟨r,hr,uniformCauchySeqOn_closedBall_of_sphere F hF 0 r
    ((le_max_right R 0).trans_lt hr) hc.uniformCauchySeqOn⟩

/-- The same sequence converges at every point, including the exceptional points. -/
theorem tendsto_entireSequenceLimit (F : ℕ → ℂ → ℂ) (hF : ∀ n, Differentiable ℂ (F n))
    (S : Set ℂ) (hS : S.Countable) (g : ℂ → ℂ) (h : TendstoLocallyUniformlyOn F g atTop Sᶜ)
    (z : ℂ) : Tendsto (fun n => F n z) atTop (𝓝 (entireSequenceLimit F z)) := by
  obtain ⟨r,hr,hc⟩ := exists_large_uniformCauchySeqOn_closedBall F hF S hS g h ‖z‖
  exact (hc.cauchySeq (show z ∈ closedBall 0 r from by
    simpa only [mem_closedBall, dist_zero_right] using ((le_max_left ‖z‖ 0).trans_lt hr).le)).tendsto_limUnder

/-- The locally uniform limit extends across the whole countable exceptional set. -/
theorem tendstoLocallyUniformlyOn_entireSequenceLimit (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, Differentiable ℂ (F n)) (S : Set ℂ) (hS : S.Countable) (g : ℂ → ℂ)
    (h : TendstoLocallyUniformlyOn F g atTop Sᶜ) :
    TendstoLocallyUniformlyOn F (entireSequenceLimit F) atTop Set.univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z _
  obtain ⟨r,hr,hc⟩ := exists_large_uniformCauchySeqOn_closedBall F hF S hS g h ‖z‖
  refine ⟨closedBall 0 r,nhdsWithin_le_nhds ?_,hc.tendstoUniformlyOn_of_tendsto
    (fun x _ => tendsto_entireSequenceLimit F hF S hS g h x)⟩
  apply mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
  simpa only [mem_ball, dist_zero_right] using (le_max_left ‖z‖ 0).trans_lt hr

/-- The extension is entire, not merely continuous at the filled points. -/
theorem analyticOnNhd_entireSequenceLimit (F : ℕ → ℂ → ℂ) (hF : ∀ n, Differentiable ℂ (F n))
    (S : Set ℂ) (hS : S.Countable) (g : ℂ → ℂ) (h : TendstoLocallyUniformlyOn F g atTop Sᶜ) :
    AnalyticOnNhd ℂ (entireSequenceLimit F) Set.univ :=
  ((tendstoLocallyUniformlyOn_entireSequenceLimit F hF S hS g h).differentiableOn
    (Filter.Eventually.of_forall (fun n => (hF n).differentiableOn)) isOpen_univ).analyticOnNhd isOpen_univ

/-- The extended function retains every already determined off-exceptional value. -/
theorem entireSequenceLimit_eqOn (F : ℕ → ℂ → ℂ) (hF : ∀ n, Differentiable ℂ (F n))
    (S : Set ℂ) (hS : S.Countable) (g : ℂ → ℂ) (h : TendstoLocallyUniformlyOn F g atTop Sᶜ) :
    Sᶜ.EqOn (entireSequenceLimit F) g :=
  fun z hz => tendsto_nhds_unique (tendsto_entireSequenceLimit F hF S hS g h z) (h.tendsto_at hz)

end NLS.ComplexAnalysis
