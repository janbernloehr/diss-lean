import NLS.ComplexAnalysis.QuadraticCauchyUniqueness
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! # Source stationarity of analytic quadratic-equation solutions

When the two symmetric coefficients and the right-hand side have zero
source variation, differentiating the equation gives a homogeneous
equation for the variation of its analytic solution. A contained root
and analytic uniqueness force that variation to vanish.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_quadratic_equation_eq_zero_of_stationary_data
    (H N : ℂ × E → ℂ) (M G : E → ℂ) (Ω : Set ℂ) (V : Set E)
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hconn : IsPreconnected Ω)
    (α h : E) (hα : α ∈ V) (u v : ℂ) (hu : u ∈ Ω)
    (hMvalue : M α = (u+v)/2) (hGvalue : G α = (v-u)^2)
    (hM : DifferentiableAt ℂ M α) (hG : DifferentiableAt ℂ G α)
    (hMGzero : (fderiv ℂ M α) h = 0 ∧ (fderiv ℂ G α) h = 0)
    (hH : AnalyticOnNhd ℂ H (Ω ×ˢ V))
    (heq : ∀ ψ ∈ V, ∀ w ∈ Ω,
      quadraticRootPolynomial (M ψ) (G ψ/4) w*deriv (fun z => H (z,ψ)) w+
        (w-M ψ)*H (w,ψ) = N (w,ψ))
    (hNzero : ∀ w ∈ Ω, (fderiv ℂ (fun ψ : E => N (w,ψ)) α) h = 0)
    (z : ℂ) (hz : z ∈ Ω) :
    (fderiv ℂ (fun ψ : E => H (z,ψ)) α) h = 0 := by
  let X := Ω ×ˢ V
  have hX : IsOpen X := hΩ.prod hV
  let J : ℂ → ℂ := fun w => (fderiv ℂ (fun ψ : E => H (w,ψ)) α) h
  let ev₀ : ((ℂ × E) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  let ev₁ : ((ℂ × E) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hJjoint : AnalyticOnNhd ℂ (fun t => (fderiv ℂ H t) (0,h)) X :=
    ev₀.comp_analyticOnNhd hH.fderiv
  have hCjoint : AnalyticOnNhd ℂ (fun t => (fderiv ℂ H t) (1,0)) X :=
    ev₁.comp_analyticOnNhd hH.fderiv
  have hJ : AnalyticOnNhd ℂ J Ω := by
    intro w hw
    have ha := (hJjoint (w,α) ⟨hw,hα⟩).comp
      (f := fun t : ℂ => (t,α)) (analyticAt_id.prod analyticAt_const)
    have hnear : J =ᶠ[𝓝 w] (fun t => (fderiv ℂ H (t,α)) (0,h)) := by
      filter_upwards [hΩ.mem_nhds hw] with t ht
      dsimp only [J]
      rw [fderiv_source_section_eq_joint H t α (hH (t,α) ⟨ht,hα⟩).differentiableAt]
      simp
    exact ha.congr hnear.symm
  have hzero (w : ℂ) (hw : w ∈ Ω) :
      quadraticRootPolynomial (M α) (G α/4) w*deriv J w+(w-M α)*J w = 0 := by
    let B : E → ℂ := fun ψ => w-M ψ
    let C : E → ℂ := fun ψ => deriv (fun t => H (t,ψ)) w
    have hHs : DifferentiableAt ℂ (fun ψ : E => H (w,ψ)) α :=
      ((hH (w,α) ⟨hw,hα⟩).comp
        (f := fun ψ : E => (w,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hC : DifferentiableAt ℂ C α := by
      have ha := (hCjoint (w,α) ⟨hw,hα⟩).comp
        (f := fun ψ : E => (w,ψ)) (analyticAt_const.prod analyticAt_id)
      have hnear : C =ᶠ[𝓝 α] (fun ψ => (fderiv ℂ H (w,ψ)) (1,0)) := by
        filter_upwards [hV.mem_nhds hα] with ψ hψ
        exact deriv_spectral_section_eq_fderiv H w ψ (hH (w,ψ) ⟨hw,hψ⟩).differentiableAt
      exact (ha.congr hnear.symm).differentiableAt
    have hB := (hasFDerivAt_const w α).fun_sub hM.hasFDerivAt
    have hpoly := (hB.pow 2).fun_sub (hG.hasFDerivAt.mul_const (4 : ℂ)⁻¹)
    have hpolyzero : (fderiv ℂ (fun ψ : E =>
        quadraticRootPolynomial (M ψ) (G ψ/4) w) α) h = 0 := by
      have ht := congrArg (fun L : E →L[ℂ] ℂ => L h) hpoly.fderiv
      change (fderiv ℂ (fun ψ : E => quadraticRootPolynomial (M ψ) (G ψ/4) w) α) h = _ at ht
      simp only [sub_apply,smul_apply,smul_eq_mul,zero_apply,hMGzero.1,hMGzero.2,
        sub_self,mul_zero] at ht
      exact ht
    have hBzero : (fderiv ℂ B α) h = 0 := by
      rw [hB.fderiv]
      simp [hMGzero.1]
    have hL := (hpoly.fun_mul hC.hasFDerivAt).fun_add (hB.fun_mul hHs.hasFDerivAt)
    have hnear : (fun ψ : E => quadraticRootPolynomial (M ψ) (G ψ/4) w*C ψ+
        B ψ*H (w,ψ)) =ᶠ[𝓝 α] (fun ψ => N (w,ψ)) := by
      filter_upwards [hV.mem_nhds hα] with ψ hψ
      exact heq ψ hψ w hw
    have ht := congrArg (fun L : E →L[ℂ] ℂ => L h) hnear.fderiv_eq
    have hLd := hL.fderiv
    change fderiv ℂ (fun ψ : E => quadraticRootPolynomial (M ψ) (G ψ/4) w*C ψ+
      B ψ*H (w,ψ)) α = _ at hLd
    rw [hLd,hNzero w hw] at ht
    have hpEval := congrArg (fun L : E →L[ℂ] ℂ => L h) hpoly.fderiv
    change (fderiv ℂ (fun ψ : E => quadraticRootPolynomial (M ψ) (G ψ/4) w) α) h = _ at hpEval
    have hBEval := congrArg (fun L : E →L[ℂ] ℂ => L h) hB.fderiv
    have hcomm := fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source H X hX hH w α ⟨hw,hα⟩ h
    simp only [add_apply,smul_apply,smul_eq_mul] at ht
    rw [← hpEval,hpolyzero,← hBEval,hBzero,mul_zero,mul_zero,add_zero,add_zero,hcomm] at ht
    exact ht
  apply quadratic_equation_homogeneous_eq_zero u v J Ω hΩ hconn hu hJ _ z hz
  intro w hw
  simpa only [hMvalue,hGvalue] using hzero w hw

end NLS.ComplexAnalysis
