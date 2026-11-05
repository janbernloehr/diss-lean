import NLS.KdV.HillDirichletAnalyticCircleData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillDirichletCirclePhase (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  -(hillDirichletGapCosine q hq hr n hn+I*hillDirichletGapSine q hq hr n hn)

theorem hillDirichletCirclePhase_norm (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) :
    ‖hillDirichletCirclePhase q hq hr n hn‖ = 1 := by
  obtain ⟨e,he,_,hcos,hsin⟩ := exists_hillDirichlet_terminal_angle q hq hr n hn hgap
  have him : e.im = 0 := im_eq_zero_of_mem_real_segment (-Real.pi) Real.pi e (by simpa only [ofReal_neg] using he)
  rw [hillDirichletCirclePhase,← hcos,← hsin,mul_comm I,← Complex.exp_mul_I,norm_neg,Complex.norm_exp]
  simp only [mul_re,I_re,mul_zero,I_im,mul_one,him,sub_zero,Real.exp_zero]

theorem exists_hillDirichletCirclePhase_analytic_extension (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        F (SpectralWeight.one.toCoeff p.val) = hillDirichletCirclePhase p.val p.property.1 p.property.2 n hn := by
  obtain ⟨d,μ,S,hd,hμ,hS,hd0,_,_,_,hmatch⟩ := exists_hillDirichlet_analytic_circle_data q hq hr n hn hgap
  let F : Coeff 2 → ℂ := fun p => -((μ p-hillLocalGapMidpoint q hq hr n p)/d p+I*S p)
  obtain ⟨V,_,hqV,hmidV,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr n hn
  have hmid := hmidV _ hqV
  have hF : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) :=
    (((hμ.sub hmid).div hd (hd0 ▸ ofReal_ne_zero.mpr hgap)).add (analyticAt_const.mul hS)).neg
  refine ⟨F,hF,?_⟩
  filter_upwards [hmatch] with p hp
  dsimp only [F,hillDirichletCirclePhase,hillDirichletGapCosine]
  rw [hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2]

theorem continuousAt_hillDirichletCirclePhase_open (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) :
    ContinuousAt (fun p : RealPeriodOneHillPotential => hillDirichletCirclePhase p.val p.property.1 p.property.2 n hn)
      (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) := by
  obtain ⟨F,hF,hmatch⟩ := exists_hillDirichletCirclePhase_analytic_extension q hq hr n hn hgap
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => F (P p)) (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) :=
    ContinuousAt.comp (f := P) hF.continuousAt hP.continuousAt
  exact hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm hmatch)

end NLS.KdV
