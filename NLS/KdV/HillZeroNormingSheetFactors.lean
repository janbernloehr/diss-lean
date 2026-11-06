import NLS.KdV.HillCharacteristicLogSheet
import NLS.KdV.HillLogNormingCotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- An analytic multiple of the actual characteristic sheet has, at every zero
physical norming coordinate, the exact genuine log-norming cotangent. Open
endpoints and collapsed gaps are included in the same formula. -/
theorem hillDirichletSheetFactor_zero_norming_fderiv
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0)
    (μ F : Coeff 2 → ℂ)
    (hμ : AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q.val))
    (hF : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q.val))
    (hμ0 : μ (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (hroot : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),hillL2DirichletCharacteristic p (μ p)=0)
    (h : Coeff 2) :
    (fderiv ℂ (fun p => F p*hillDirichletSheetRoot p (μ p)) (SpectralWeight.one.toCoeff q.val)) h=
      (F (SpectralWeight.one.toCoeff q.val)*((-1 : ℂ)^k*2))*
        hillPhysicalDirectionPairing h (hillLogNormingGradientCurve q k hk) := by
  let p0 := SpectralWeight.one.toCoeff q.val
  let M : Coeff 2 → ℂ := fun p => (-1 : ℂ)^k*hillL2DirichletSlope p (μ p)
  let G : Coeff 2 → ℂ := fun p => Complex.log (M p)
  obtain ⟨hG,hGbase⟩ := hillDirichletLogBranch_analytic_base q k hk μ hμ hμ0
  have hGa : AnalyticAt ℂ G p0 := hG
  have hG0 : G p0=0 := by
    dsimp only [G,M,p0]
    rw [hGbase,hlog,ofReal_zero]
  have hM : AnalyticAt ℂ M p0 :=
    analyticAt_const.mul ((analyticOnNhd_hillL2DirichletSlope_joint (μ p0,p0) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id))
  have hMn : M p0≠0 := by
    dsimp only [M,p0]
    rw [hμ0,←hillDirichletMultiplier_ofReal]
    exact ofReal_ne_zero.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 k hk).ne'
  have hrel : (fun p => F p*hillDirichletSheetRoot p (μ p))=ᶠ[𝓝 p0]
      (fun p => F p*((-1 : ℂ)^k*2*Complex.sinh (G p))) := by
    filter_upwards [hroot,hM.continuousAt.eventually_ne hMn] with p hp hm
    rw [hillDirichletSheetRoot_eq_signed_sinh_of_exp p (μ p) (G p) k hp (Complex.exp_log hm)]
  have hd := (hF.differentiableAt.hasFDerivAt.mul
    (hGa.differentiableAt.hasFDerivAt.csinh.const_mul ((-1 : ℂ)^k*2))).congr_of_eventuallyEq hrel
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,hG0,show G (SpectralWeight.one.toCoeff q.val)=0 from hG0,Complex.sinh_zero,Complex.cosh_zero,
    mul_zero,one_mul]
  rw [hillLogNormingGradient_represents_branch q k hk μ hμ hμ0 hroot h,
    hillPhysicalDirectionPairing_apply]
  ring

end NLS.KdV
