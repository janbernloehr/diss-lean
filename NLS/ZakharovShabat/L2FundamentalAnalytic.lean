import NLS.ZakharovShabat.L2VolterraInverse
import NLS.ZakharovShabat.L2HermitianOperatorBound

/-! # Joint parameter regularity of the original L2 fundamental solution

The bounded L2 coefficient map and the globally invertible actual Volterra
operator give analyticity in frequency and potential in the uniform curve
norm. Evaluation gives joint continuity in time and parameters on [0,1].
-/
noncomputable section
open Set Complex Filter Topology
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The full forcing inverse depends analytically on frequency and the physical L2 potential. -/
theorem analyticOnNhd_l2SolutionOperator : AnalyticOnNhd ℂ l2SolutionOperator univ := by
  intro q _
  have hV : AnalyticAt ℂ l2Volterra q := by
    convert! ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (F := Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ)) l2VolterraCoefficientMap q
  exact (analyticOnNhd_inverse (𝕜 := ℂ) (A := Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ)) _
    (isUnit_one_sub_l2Volterra q)).comp (f := fun r => 1-l2Volterra r)
      (analyticAt_const.sub hV)

theorem continuous_l2SolutionOperator : Continuous l2SolutionOperator :=
  continuous_iff_continuousAt.mpr (fun q => (analyticOnNhd_l2SolutionOperator q (mem_univ q)).continuousAt)

/-- Every continuous input recovers the original full Volterra inverse. -/
theorem l2SolutionOperator_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2SolutionOperator (z,continuousPotentialL2Class φ) = solutionOperator (classicalCoefficientCurveCLM (z,φ)) := by
  unfold l2SolutionOperator solutionOperator
  rw [l2Volterra_of_continuous]

/-- The L2-based forcing bound passes to all original physical L2 inputs. -/
theorem norm_l2SolutionOperator_le (q : ℂ × IntervalPairL2) :
    ‖l2SolutionOperator q‖ ≤ Real.exp (‖q.1‖+‖q.2‖) := by
  let : NeBot (continuousPotentialL2Filter q.2) := continuousPotentialL2Filter_neBot q.2
  have hp : Tendsto continuousPotentialL2Class (continuousPotentialL2Filter q.2) (𝓝 q.2) := tendsto_comap
  have hs : Tendsto (fun φ => ‖l2SolutionOperator (q.1,continuousPotentialL2Class φ)‖)
      (continuousPotentialL2Filter q.2) (𝓝 ‖l2SolutionOperator q‖) := by
    have hc' : Continuous (fun u : IntervalPairL2 => l2SolutionOperator (q.1,u)) :=
      continuous_l2SolutionOperator.comp (continuous_const.prodMk continuous_id)
    have hc : Continuous (fun u : IntervalPairL2 => ‖l2SolutionOperator (q.1,u)‖) := by
      have hn : Continuous (fun S : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) => ‖S‖) := by
        convert! (continuous_norm (E := Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ)))
      exact hn.comp hc'
    exact hc.continuousAt.tendsto.comp hp
  have he : Tendsto (fun φ => Real.exp (‖q.1‖+‖continuousPotentialL2Class φ‖))
      (continuousPotentialL2Filter q.2) (𝓝 (Real.exp (‖q.1‖+‖q.2‖))) :=
    (continuous_const.add continuous_norm).rexp.continuousAt.tendsto.comp hp
  apply le_of_tendsto_of_tendsto hs he
  apply Filter.Eventually.of_forall
  intro φ
  dsimp only
  rw [l2SolutionOperator_of_continuous,norm_continuousPotentialL2Class]
  exact norm_classicalSolutionOperator_le_L2 φ q.1

/-- The previously constructed actual initial-value solution is analytic in the uniform curve norm. -/
theorem analyticOnNhd_l2SolutionCurve_joint (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2SolutionCurve q.2 q.1 v) univ := by
  simp_rw [l2SolutionCurve_eq_l2SolutionOperator]
  intro q _
  exact ((ContinuousLinearMap.apply ℂ (Curve (ℂ × ℂ)) (ContinuousMap.const _ v)).analyticAt _).comp
    (analyticOnNhd_l2SolutionOperator q (mem_univ q))

theorem continuous_l2SolutionCurve_joint (v : ℂ × ℂ) :
    Continuous (fun q : ℂ × IntervalPairL2 => l2SolutionCurve q.2 q.1 v) :=
  continuous_iff_continuousAt.mpr (fun q => (analyticOnNhd_l2SolutionCurve_joint v q (mem_univ q)).continuousAt)

/-- Joint time/frequency/potential continuity includes both endpoints of the physical interval. -/
theorem continuous_l2SolutionCurve_time_joint (v : ℂ × ℂ) :
    Continuous (fun qt : (ℂ × IntervalPairL2) × Icc (0 : ℝ) 1 => l2SolutionCurve qt.1.2 qt.1.1 v qt.2) :=
  continuous_eval.comp (((continuous_l2SolutionCurve_joint v).comp continuous_fst).prodMk continuous_snd)

/-- At each physical time the actual matrix is jointly analytic in both original parameters. -/
theorem analyticOnNhd_l2FundamentalMatrix_joint (t : Icc (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2FundamentalMatrix q.2 q.1 t) univ := by
  intro q _
  have h₁ := ((ContinuousMap.evalCLM ℂ t).analyticAt _).comp
    (analyticOnNhd_l2SolutionCurve_joint (1,0) q (mem_univ q))
  have h₂ := ((ContinuousMap.evalCLM ℂ t).analyticAt _).comp
    (analyticOnNhd_l2SolutionCurve_joint (0,1) q (mem_univ q))
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  fin_cases i <;> fin_cases j
  · exact analyticAt_fst.comp h₁
  · exact analyticAt_fst.comp h₂
  · exact analyticAt_snd.comp h₁
  · exact analyticAt_snd.comp h₂

theorem continuous_l2FundamentalMatrix_time_joint :
    Continuous (fun qt : (ℂ × IntervalPairL2) × Icc (0 : ℝ) 1 => l2FundamentalMatrix qt.1.2 qt.1.1 qt.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact (continuous_l2SolutionCurve_time_joint (1,0)).fst
  · exact (continuous_l2SolutionCurve_time_joint (0,1)).fst
  · exact (continuous_l2SolutionCurve_time_joint (1,0)).snd
  · exact (continuous_l2SolutionCurve_time_joint (0,1)).snd

/-- The original L2 fundamental matrix has determinant one at every physical time. -/
@[simp] theorem det_l2FundamentalMatrix (u : IntervalPairL2) (z : ℂ)
    (t : Icc (0 : ℝ) 1) : (l2FundamentalMatrix u z t).det = 1 := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  have hp : Tendsto continuousPotentialL2Class (continuousPotentialL2Filter u) (𝓝 u) := tendsto_comap
  have hc : Continuous (fun v : IntervalPairL2 => l2FundamentalMatrix v z t) :=
    continuous_iff_continuousAt.mpr (fun v =>
      ((analyticOnNhd_l2FundamentalMatrix_joint t (z,v) (mem_univ _)).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt))
  have hd := hc.matrix_det.continuousAt.tendsto.comp hp
  have he : (fun φ => (l2FundamentalMatrix (continuousPotentialL2Class φ) z t).det) =
      fun _ : Curve (ℂ × ℂ) => (1 : ℂ) := by
    funext φ
    rw [l2FundamentalMatrix_of_continuous,det_classicalFundamentalMatrix]
  change Tendsto (fun φ => (l2FundamentalMatrix (continuousPotentialL2Class φ) z t).det) _ _ at hd
  rw [he] at hd
  exact tendsto_nhds_unique hd tendsto_const_nhds

end NLS.ZakharovShabat
