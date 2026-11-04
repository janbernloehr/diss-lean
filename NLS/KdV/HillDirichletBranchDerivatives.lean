import NLS.KdV.HillDirichletAnalyticNorming
import NLS.ComplexAnalysis.MovingSpectralParameter
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillDirichlet_branch_fderiv_apply
    (q : Coeff 2) (hq : IsRealHillPotential q) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a q)
    (hz : ∀ᶠ p in 𝓝 q, hillL2DirichletCharacteristic p (a p)=0) (h : Coeff 2) :
    (fderiv ℂ a q) h=
      -((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletCharacteristic p (a q)) q) h)/
        deriv (hillL2DirichletCharacteristic q) (a q) := by
  let F : ℂ × Coeff 2 → ℂ := fun p => hillL2DirichletCharacteristic p.2 p.1
  have hF : DifferentiableAt ℂ F (a q,q) :=
    (analyticOnNhd_hillL2DirichletCharacteristic_joint (a q,q) (mem_univ _)).differentiableAt
  have hd := fderiv_moving_spectral_parameter F a q hF ha.differentiableAt
  have heq : (fun p : Coeff 2 => F (a p,p))=ᶠ[𝓝 q] (fun _ => (0 : ℂ)) := hz
  have hzero : fderiv ℂ (fun p : Coeff 2 => F (a p,p)) q=0 := by rw [heq.fderiv_eq];simp
  rw [hzero] at hd
  have hp := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd
  simp only [zero_apply,add_apply,
    smul_apply,smul_eq_mul] at hp
  apply (eq_div_iff (hillL2DirichletCharacteristic_deriv_ne_zero q hq (a q) heq.eq_of_nhds)).mpr
  change (fderiv ℂ a q) h * deriv (fun z : ℂ => F (z,q)) (a q)=
    -(fderiv ℂ (fun p : Coeff 2 => F (a q,p)) q) h
  linear_combination -hp

theorem hillDirichlet_log_branch_fderiv_apply
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (h : Coeff 2) :
    (fderiv ℂ (fun p : Coeff 2 => log ((-1 : ℂ)^n*hillL2DirichletSlope p (a p)))
      (SpectralWeight.one.toCoeff q.val)) h=
      ((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p (a (SpectralWeight.one.toCoeff q.val)))
        (SpectralWeight.one.toCoeff q.val)) h+
       deriv (hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)) (a (SpectralWeight.one.toCoeff q.val))*
        (fderiv ℂ a (SpectralWeight.one.toCoeff q.val)) h)/
       hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val) (a (SpectralWeight.one.toCoeff q.val)) := by
  let p := SpectralWeight.one.toCoeff q.val
  let F : ℂ × Coeff 2 → ℂ := fun z => hillL2DirichletSlope z.2 z.1
  let G (r : Coeff 2) := F (a r,r)
  let s : ℂ := (-1)^n
  have hF : AnalyticAt ℂ F (a p,p) := analyticOnNhd_hillL2DirichletSlope_joint _ (mem_univ _)
  have hG : AnalyticAt ℂ G p := hF.comp (f := fun r : Coeff 2 => (a r,r)) (ha.prod analyticAt_id)
  have hM : s*G p=(hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [G,F,s,p]
    rw [ha0,← hillDirichletMultiplier_ofReal]
  have hslit : s*G p∈slitPlane := by
    rw [hM]
    exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)
  have hder := (hG.differentiableAt.hasFDerivAt.const_mul s).clog hslit
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hder.fderiv
  have hmove := fderiv_moving_spectral_parameter F a p hF.differentiableAt ha.differentiableAt
  have hs : s≠0 := pow_ne_zero _ (by norm_num)
  have hg : G p≠0 := by
    intro hh
    exact slitPlane_ne_zero hslit (by rw [hh,mul_zero])
  change (fderiv ℂ (fun r : Coeff 2 => log (s*G r)) p) h=_
  rw [hd]
  change (s*G p)⁻¹*(s*(fderiv ℂ G p) h)=_
  rw [hmove]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change (s*G p)⁻¹*(s*((fderiv ℂ (fun r : Coeff 2 => F (a p,r)) p) h+
    deriv (fun z : ℂ => F (z,p)) (a p)*(fderiv ℂ a p) h))=
    ((fderiv ℂ (fun r : Coeff 2 => F (a p,r)) p) h+
      deriv (fun z : ℂ => F (z,p)) (a p)*(fderiv ℂ a p) h)/G p
  field_simp

end NLS.KdV
