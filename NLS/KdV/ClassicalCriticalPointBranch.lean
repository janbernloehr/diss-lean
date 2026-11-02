import NLS.KdV.FreeFrequencyPsi
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Actual Hill critical points near the free potential

The zeros of the actual energy discriminant derivative are constructed
by the analytic implicit function theorem, using the proved nonzero free
second derivative. No selected spectral zero is supplied as a hypothesis.
The neighborhoods depend on the mode; uniform tail estimates and global
labeling remain separate requirements.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.KdV

/-- The actual energy derivative of the continuous-potential discriminant. -/
def classicalHillDiscriminantDerivative (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  deriv (classicalHillDiscriminant t.2) t.1

theorem analyticOnNhd_classicalHillDiscriminantDerivative :
    AnalyticOnNhd ℂ classicalHillDiscriminantDerivative univ :=
  ComplexAnalysis.analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant t.2 t.1)
    univ isOpen_univ analyticOnNhd_classicalHillDiscriminant_joint

theorem analyticOnNhd_classicalHillDiscriminantSecondDerivative :
    AnalyticOnNhd ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
      deriv (deriv (classicalHillDiscriminant t.2)) t.1) univ :=
  ComplexAnalysis.analyticOnNhd_spectral_deriv_of_analyticOnNhd
    classicalHillDiscriminantDerivative univ isOpen_univ
    analyticOnNhd_classicalHillDiscriminantDerivative

/-- Every positive free critical point deforms to an actual analytic
critical point, retaining nonzero second derivative on an open complex
potential neighborhood. -/
theorem exists_classicalHill_critical_point_branch (n : ℕ+) :
    ∃ μ : NLS.LinearVolterra.Curve ℂ → ℂ,
      ∃ V : Set (NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ 0 ∈ V ∧
        μ 0 = freeHillEnergy n ∧ AnalyticOnNhd ℂ μ V ∧
        ∀ q ∈ V, deriv (classicalHillDiscriminant q) (μ q) = 0 ∧
          deriv (deriv (classicalHillDiscriminant q)) (μ q) ≠ 0 := by
  let F := classicalHillDiscriminantDerivative
  let a := freeHillEnergy n
  have hF : AnalyticAt ℂ F (a,0) :=
    analyticOnNhd_classicalHillDiscriminantDerivative (a,0) (mem_univ _)
  have hz : F (a,0) = 0 := deriv_classicalHillDiscriminant_free_energy n
  have hs : deriv (deriv (classicalHillDiscriminant 0)) a ≠ 0 :=
    deriv_deriv_classicalHillDiscriminant_free_energy_ne_zero n
  have hd := ((analyticOnNhd_classicalHillDiscriminant 0 a (mem_univ _)).deriv).differentiableAt.hasDerivAt
  have hpartial : (fderiv ℂ F (a,0)).comp
      (ContinuousLinearMap.inl ℂ ℂ (NLS.LinearVolterra.Curve ℂ)) =
      ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv (classicalHillDiscriminant 0)) a) := by
    have hc := hF.differentiableAt.hasFDerivAt.comp
      (f := fun w : ℂ => (w,(0 : NLS.LinearVolterra.Curve ℂ))) a
      (hasFDerivAt_prodMk_left a (0 : NLS.LinearVolterra.Curve ℂ))
    exact hc.unique hd.hasFDerivAt
  have hbij : Function.Bijective ((fderiv ℂ F (a,0)).comp
      (ContinuousLinearMap.inl ℂ ℂ (NLS.LinearVolterra.Curve ℂ))) := by
    rw [hpartial]
    constructor
    · intro x y hxy
      exact mul_right_cancel₀ hs (by simpa using hxy)
    · intro w
      refine ⟨w/deriv (deriv (classicalHillDiscriminant 0)) a, ?_⟩
      exact div_mul_cancel₀ w hs
  obtain ⟨μ, hμ, hμ0, hzero⟩ :=
    ComplexAnalysis.exists_analytic_implicitBanachRoot F a 0 hF hz hbij
  have hcont : Continuous (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
      deriv (deriv (classicalHillDiscriminant t.2)) t.1) :=
    continuousOn_univ.mp analyticOnNhd_classicalHillDiscriminantSecondDerivative.continuousOn
  have hsimple : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ),
      deriv (deriv (classicalHillDiscriminant q)) (μ q) ≠ 0 :=
    (hcont.continuousAt.comp (hμ.continuousAt.prodMk continuousAt_id)).eventually_ne
      (by simpa only [Function.comp_apply, id_eq, hμ0] using hs)
  obtain ⟨r, hr, han⟩ := hμ.exists_ball_analyticOnNhd
  obtain ⟨W, hWsub, hW, h0W⟩ := _root_.mem_nhds_iff.mp (hzero.and hsimple)
  refine ⟨μ, W ∩ Metric.ball 0 r, hW.inter Metric.isOpen_ball,
    ⟨h0W, Metric.mem_ball_self hr⟩, hμ0, han.mono inter_subset_right, ?_⟩
  intro q hq
  exact hWsub hq.1

end NLS.KdV
