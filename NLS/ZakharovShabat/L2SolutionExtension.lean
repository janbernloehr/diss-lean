import NLS.ZakharovShabat.ClassicalL2Stability
import NLS.ZakharovShabat.ContinuousPotentialL2Density

/-! # The approximation-independent L2 extension of classical solution curves

Density and uniform stability prove convergence in the complete space of
continuous solution curves. The limit is taken over all continuous potentials
approaching a given physical L2 class, not over a selected approximation.
The original Volterra identity and G.1 limit passage are separate next steps.
-/
noncomputable section
open Set Metric Filter Topology MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Continuous potentials approaching an original physical L2 class. -/
def continuousPotentialL2Filter (u : IntervalPairL2) : Filter (Curve (ℂ × ℂ)) :=
  comap continuousPotentialL2Class (𝓝 u)

theorem continuousPotentialL2Filter_neBot (u : IntervalPairL2) :
    NeBot (continuousPotentialL2Filter u) := by
  apply comap_neBot
  intro s hs
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨φ,hφ⟩ := exists_continuousPotential_L2_approximation u ε hε
  exact ⟨φ,hsub (by simpa only [mem_ball,dist_comm] using hφ)⟩

/-- Every L2-approaching family has Cauchy solution curves in the uniform norm. -/
theorem cauchy_classicalSolutionCurve_L2 (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    Cauchy (map (fun φ => classicalSolutionCurve φ z v) (continuousPotentialL2Filter u)) := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance,?_⟩
  intro ε hε
  let R := ‖u‖+1
  let K := ‖v‖*Real.exp (2*‖z‖+2*R)
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  let δ := min (1:ℝ) (ε/(4*(K+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  let S := continuousPotentialL2Class ⁻¹' ball u δ
  refine ⟨(fun φ => classicalSolutionCurve φ z v) '' S,?_,?_⟩
  · apply mem_map.mpr
    apply mem_comap.mpr
    exact ⟨ball u δ,ball_mem_nhds u hδ,fun φ hφ => ⟨φ,hφ,rfl⟩⟩
  · rintro _ ⟨φ,hφ,rfl⟩ _ ⟨ψ,hψ,rfl⟩
    have hφd : dist (continuousPotentialL2Class φ) u < δ := hφ
    have hψd : dist (continuousPotentialL2Class ψ) u < δ := hψ
    have hφR : ‖continuousPotentialL2Class φ‖ ≤ R :=
      (norm_le_norm_add_const_of_dist_le hφd.le).trans
        (add_le_add (le_refl _) (min_le_left (1:ℝ) (ε/(4*(K+1)))))
    have hψR : ‖continuousPotentialL2Class ψ‖ ≤ R :=
      (norm_le_norm_add_const_of_dist_le hψd.le).trans
        (add_le_add (le_refl _) (min_le_left (1:ℝ) (ε/(4*(K+1)))))
    have hd : dist (continuousPotentialL2Class φ) (continuousPotentialL2Class ψ) < 2*δ := by
      have h := dist_triangle (continuousPotentialL2Class φ) u (continuousPotentialL2Class ψ)
      rw [dist_comm u (continuousPotentialL2Class ψ)] at h
      linarith
    have hδε : 4*(K+1)*δ ≤ ε := by
      have h : δ ≤ ε/(4*(K+1)) := min_le_right (1:ℝ) (ε/(4*(K+1)))
      nlinarith [(le_div_iff₀ (by positivity : 0 < 4*(K+1))).mp h]
    have hsmall : K*(2*δ) < ε := by nlinarith
    exact (dist_classicalSolutionCurve_le_L2 φ ψ z v R hφR hψR).trans_lt
      ((mul_le_mul_of_nonneg_left hd.le hK).trans_lt hsmall)

/-- The uniform limit of actual classical solution curves at a physical L2 potential. -/
def l2SolutionCurve (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  limUnder (continuousPotentialL2Filter u) (fun φ => classicalSolutionCurve φ z v)

/-- Existence of the defining limit; no convergence assumption is built into the definition. -/
theorem tendsto_classicalSolutionCurve_L2 (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    Tendsto (fun φ => classicalSolutionCurve φ z v) (continuousPotentialL2Filter u)
      (𝓝 (l2SolutionCurve u z v)) := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  obtain ⟨w,hw⟩ := cauchy_map_iff_exists_tendsto.mp (cauchy_classicalSolutionCurve_L2 u z v)
  rw [l2SolutionCurve,hw.limUnder_eq]
  exact hw

/-- Any convergent approximation, along any filter, gives the same uniform solution limit. -/
theorem tendsto_solutionCurve_of_tendsto_L2 {ι : Type*} {l : Filter ι}
    (φ : ι → Curve (ℂ × ℂ)) (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (hφ : Tendsto (fun i => continuousPotentialL2Class (φ i)) l (𝓝 u)) :
    Tendsto (fun i => classicalSolutionCurve (φ i) z v) l (𝓝 (l2SolutionCurve u z v)) :=
  (tendsto_classicalSolutionCurve_L2 u z v).comp (tendsto_comap_iff.mpr hφ)

/-- Exact recovery of the previously constructed classical solution. -/
@[simp] theorem l2SolutionCurve_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    l2SolutionCurve (continuousPotentialL2Class φ) z v = classicalSolutionCurve φ z v := by
  have h := tendsto_solutionCurve_of_tendsto_L2 (l := (atTop : Filter ℕ)) (fun _ => φ)
    (continuousPotentialL2Class φ) z v tendsto_const_nhds
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Every extended solution retains its actual initial value. -/
@[simp] theorem l2SolutionCurve_zero (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    l2SolutionCurve u z v ⟨0,by constructor <;> norm_num⟩ = v := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  have h := ((continuous_eval_const ⟨0,by constructor <;> norm_num⟩).tendsto
    (l2SolutionCurve u z v)).comp (tendsto_classicalSolutionCurve_L2 u z v)
  simp only [Function.comp_def,classicalSolutionCurve_apply,classicalSolution_zero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Growth of the extended solution curve in the actual physical L2 norm. -/
theorem norm_l2SolutionCurve_le (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    ‖l2SolutionCurve u z v‖ ≤ ‖v‖*Real.exp (‖z‖+‖u‖) := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  have hs := (tendsto_classicalSolutionCurve_L2 u z v).norm
  have hc : Continuous (fun w : IntervalPairL2 => ‖v‖*Real.exp (‖z‖+‖w‖)) := by fun_prop
  have hp : Tendsto continuousPotentialL2Class (continuousPotentialL2Filter u) (𝓝 u) := tendsto_comap
  apply le_of_tendsto_of_tendsto hs (hc.continuousAt.tendsto.comp hp)
  apply Eventually.of_forall
  intro φ
  change ‖classicalSolutionCurve φ z v‖ ≤ ‖v‖*Real.exp (‖z‖+‖continuousPotentialL2Class φ‖)
  rw [norm_continuousPotentialL2Class]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))).mpr
  intro t
  rw [classicalSolutionCurve_apply]
  exact norm_classicalSolution_le_exp_L2 φ z v t

/-- The zero initial vector stays zero, including for arbitrary physical L2 potentials. -/
@[simp] theorem l2SolutionCurve_zero_initial (u : IntervalPairL2) (z : ℂ) :
    l2SolutionCurve u z 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa using norm_l2SolutionCurve_le u z 0

/-- At zero potential the extension is exactly the original free solution. -/
@[simp] theorem l2SolutionCurve_free (z : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    l2SolutionCurve 0 z v t = classicalFreeVector z v t := by
  rw [← continuousPotentialL2Class_zero, l2SolutionCurve_of_continuous,
    classicalSolutionCurve_apply, classicalSolution_free]
  rfl

end NLS.ZakharovShabat
