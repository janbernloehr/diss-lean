import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Order.Field

/-! # Unbounded frequencies obstruct convergence of continuous trajectories

If nonzero amplitudes converge while their real frequencies tend to
positive infinity, the exponential trajectories cannot converge uniformly
on any positive time interval. At times pi/frequency tending to zero the
phase is minus one, whereas continuity of a limiting trajectory would
force the value at time zero.
-/
noncomputable section
open Set Filter Topology
namespace NLS.Dynamics

/-- Rapid phase rotation prevents convergence in a compact continuous-trajectory space. -/
theorem not_tendsto_phase_trajectories {ι : Type*} {l : Filter ι} [NeBot l]
    (T : ℝ) (hT : 0 < T) (freq : ι → ℝ) (amp : ι → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hfreq : Tendsto freq l atTop) (hamp : Tendsto amp l (𝓝 a))
    (g : ι → C(Icc (0 : ℝ) T,ℂ))
    (he : ∀ j (τ : Icc (0 : ℝ) T), g j τ = Complex.exp (((τ.val*freq j : ℝ) : ℂ)*Complex.I)*amp j)
    (G : C(Icc (0 : ℝ) T,ℂ)) : ¬ Tendsto g l (𝓝 G) := by
  intro hg
  let z : Icc (0 : ℝ) T := ⟨0,le_rfl,hT.le⟩
  have hz : G z = a := by
    have h := (continuous_eval_const z).tendsto G |>.comp hg
    have he0 (j : ι) : g j z = amp j := by simp [he,z]
    change Tendsto (fun j => g j z) l (𝓝 (G z)) at h
    simp only [he0] at h
    exact tendsto_nhds_unique h hamp
  let time (j : ι) : Icc (0 : ℝ) T :=
    ⟨min T (max 0 (Real.pi/freq j)),le_min hT.le (le_max_left _ _),min_le_left _ _⟩
  have hdiv : Tendsto (fun j => Real.pi/freq j) l (𝓝 (0 : ℝ)) := hfreq.const_div_atTop Real.pi
  have htime : Tendsto time l (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    have hh := (tendsto_const_nhds (x := T)).min ((tendsto_const_nhds (x := (0 : ℝ))).max hdiv)
    simpa only [max_self,min_eq_right hT.le] using hh
  have hvalue : Tendsto (fun j => g j (time j)) l (𝓝 (G z)) :=
    continuous_eval.continuousAt.tendsto.comp (hg.prodMk_nhds htime)
  have hphase : (fun j => g j (time j)) =ᶠ[l] (fun j => -amp j) := by
    filter_upwards [hfreq.eventually (eventually_gt_atTop 0),hdiv.eventually (gt_mem_nhds hT)] with j hj hsmall
    have hnonneg : 0 ≤ Real.pi/freq j := div_nonneg Real.pi_pos.le hj.le
    have ht : (time j).val = Real.pi/freq j := by
      simp only [time,max_eq_right hnonneg,min_eq_right hsmall.le]
    rw [he,ht,div_mul_cancel₀ _ hj.ne',Complex.exp_pi_mul_I]
    ring
  have hneg : Tendsto (fun j => g j (time j)) l (𝓝 (-a)) := hamp.neg.congr' hphase.symm
  have h := tendsto_nhds_unique hvalue hneg
  rw [hz] at h
  apply ha
  have htwo : (2 : ℂ)*a = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end NLS.Dynamics
