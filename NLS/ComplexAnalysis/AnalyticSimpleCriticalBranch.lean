import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import NLS.ComplexAnalysis.JointSpectralDerivative

/-! # Analytic branches of simple critical points with Banach parameters -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_analytic_simple_critical_branch (F : ℂ × E → ℂ)
    (hF : AnalyticOnNhd ℂ F univ) (a : ℂ) (q0 : E)
    (hz : deriv (fun z => F (z,q0)) a = 0)
    (hs : deriv (deriv (fun z => F (z,q0))) a ≠ 0) :
    ∃ mu : E → ℂ, ∃ V : Set E, IsOpen V ∧ q0 ∈ V ∧ mu q0 = a ∧
      AnalyticOnNhd ℂ mu V ∧ ∀ q ∈ V,
        deriv (fun z => F (z,q)) (mu q) = 0 ∧
        deriv (deriv (fun z => F (z,q))) (mu q) ≠ 0 := by
  let G : ℂ × E → ℂ := fun t => deriv (fun z => F (z,t.2)) t.1
  have hGa : AnalyticOnNhd ℂ G univ :=
    analyticOnNhd_spectral_deriv_of_analyticOnNhd F univ isOpen_univ hF
  have hG : AnalyticAt ℂ G (a,q0) := hGa _ (mem_univ _)
  have hsec : AnalyticAt ℂ (fun z => F (z,q0)) a :=
    (hF (a,q0) (mem_univ _)).comp (f := fun z : ℂ => (z,q0)) (analyticAt_id.prod analyticAt_const)
  have hd := hsec.deriv.differentiableAt.hasDerivAt
  have hpartial : (fderiv ℂ G (a,q0)).comp (ContinuousLinearMap.inl ℂ ℂ E) =
      ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv (fun z => F (z,q0))) a) := by
    have hc := hG.differentiableAt.hasFDerivAt.comp (f := fun z : ℂ => (z,q0)) a
      (hasFDerivAt_prodMk_left a q0)
    exact hc.unique hd.hasFDerivAt
  have hbij : Function.Bijective ((fderiv ℂ G (a,q0)).comp (ContinuousLinearMap.inl ℂ ℂ E)) := by
    rw [hpartial]
    constructor
    · intro x y he
      exact mul_right_cancel₀ hs (by simpa using he)
    · intro z
      exact ⟨z/deriv (deriv (fun z => F (z,q0))) a,div_mul_cancel₀ z hs⟩
  obtain ⟨mu,ha,hmu,hzero⟩ := exists_analytic_implicitBanachRoot G a q0 hG hz hbij
  have hsecond : AnalyticOnNhd ℂ (fun t : ℂ × E => deriv (deriv (fun z => F (z,t.2))) t.1) univ :=
    analyticOnNhd_spectral_deriv_of_analyticOnNhd G univ isOpen_univ hGa
  have hc := hsecond.continuous.continuousAt.comp (ha.continuousAt.prodMk continuousAt_id)
  have he : ∀ᶠ q in 𝓝 q0, deriv (deriv (fun z => F (z,q))) (mu q) ≠ 0 :=
    hc.eventually_ne (by simpa only [Function.comp_def,id_eq,hmu] using hs)
  obtain ⟨r,hr,han⟩ := ha.exists_ball_analyticOnNhd
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp (hzero.and he)
  exact ⟨mu,W ∩ Metric.ball q0 r,hW.inter Metric.isOpen_ball,⟨hqW,Metric.mem_ball_self hr⟩,
    hmu,han.mono inter_subset_right,fun q hq => hWsub hq.1⟩

end NLS.ComplexAnalysis
