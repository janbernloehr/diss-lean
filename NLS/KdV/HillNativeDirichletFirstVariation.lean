import NLS.KdV.HillPeriodOneL1Comparison
import NLS.KdV.ClassicalHillFreeEnergyDerivative
import NLS.KdV.HillNativeFreeSpectralData
import NLS.Fourier.PeriodOneTrigPairing
import NLS.ComplexAnalysis.ImplicitScalarRootDerivative

/-! Exact derivative of the ACTUAL native canonical Dirichlet coordinate
at the free potential, in every complex H-minus-one direction. The proof
uses its actual simple root equation and dense physical L1 comparison. -/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
open scoped Real
namespace NLS.KdV

def hillFreeDirichletGradient (n : ℕ+) : PeriodOneHminusOne →L[ℂ] ℂ :=
  WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0 -
    (2:ℂ)⁻¹ • (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 (n:ℤ)+
      WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 (-(n:ℤ)))

theorem hillFreeDirichletGradient_apply (n : ℕ+) (h : PeriodOneHminusOne) :
    hillFreeDirichletGradient n h = h.val 0-(h.val (n:ℤ)+h.val (-(n:ℤ)))/2 := by
  simp only [hillFreeDirichletGradient,sub_apply,smul_apply,add_apply,
    WeightedCoeff.evalCLM_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem hillHminusCanonicalDirichlet_zero_eq_sq (n : ℕ+) :
    hillHminusCanonicalDirichlet n 0 = ((π:ℂ)*n)^2 := by
  rw [hillHminusCanonicalDirichlet_zero]
  push_cast
  rfl

theorem hillHminusDirichlet_zero_eq_classical (μ : ℂ) :
    hillHminusDirichlet 0 μ = classicalHillDirichlet 0 μ := by
  simpa only [map_zero] using hillHminusDirichlet_eq_classical_L1 (0 : Coeff 1) μ

theorem hasDerivAt_hillHminusDirichlet_free_eigenvalue (n : ℕ+) :
    HasDerivAt (hillHminusDirichlet 0) ((-1:ℂ)^(n:ℕ)/(2*((π:ℂ)*n)^2)) (((π:ℂ)*n)^2) := by
  have he : hillHminusDirichlet 0 = classicalHillDirichlet 0 :=
    funext hillHminusDirichlet_zero_eq_classical
  rw [he]
  exact hasDerivAt_classicalHillDirichlet_free_eigenvalue n

theorem fderiv_hillHminusDirichlet_L1 (μ : ℂ) (a : Coeff 1) :
    (fderiv ℂ (fun q => hillHminusDirichlet q μ) 0) (periodOneL1Inclusion a) =
      (fderiv ℂ (fun Q => classicalHillDirichlet Q μ) 0) (periodOneL1PotentialCurve a) := by
  have hN : DifferentiableAt ℂ (fun q => hillHminusDirichlet q μ) 0 :=
    ((analyticOnNhd_hillHminusDirichlet_joint (μ,0) (mem_univ _)).comp
      (f := fun q : PeriodOneHminusOne => (μ,q)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hP : DifferentiableAt ℂ (fun Q => classicalHillDirichlet Q μ) 0 :=
    (analyticAt_fst.comp (analyticOnNhd_classicalHillFlow_potential μ (0,1) t 0 (mem_univ _))).differentiableAt
  have hNi : HasFDerivAt (fun q => hillHminusDirichlet q μ)
      (fderiv ℂ (fun q => hillHminusDirichlet q μ) 0) (periodOneL1Inclusion 0) := by
    simpa only [map_zero] using hN.hasFDerivAt
  have hPi : HasFDerivAt (fun Q => classicalHillDirichlet Q μ)
      (fderiv ℂ (fun Q => classicalHillDirichlet Q μ) 0) (periodOneL1PotentialCurve 0) := by
    simpa only [map_zero] using hP.hasFDerivAt
  have hNc := (hNi.comp 0 periodOneL1Inclusion.hasFDerivAt).fderiv
  have hPc := (hPi.comp 0 periodOneL1PotentialCurve.hasFDerivAt).fderiv
  change fderiv ℂ (fun b => hillHminusDirichlet (periodOneL1Inclusion b) μ) 0 = _ at hNc
  change fderiv ℂ (fun b => classicalHillDirichlet (periodOneL1PotentialCurve b) μ) 0 = _ at hPc
  have he : (fun b => hillHminusDirichlet (periodOneL1Inclusion b) μ) =
      fun b => classicalHillDirichlet (periodOneL1PotentialCurve b) μ :=
    funext (fun b => hillHminusDirichlet_eq_classical_L1 b μ)
  rw [he,hPc] at hNc
  have hh := congrArg (fun L : Coeff 1 →L[ℂ] ℂ => L a) hNc
  simpa only [ContinuousLinearMap.comp_apply,map_zero] using hh.symm

theorem fderiv_hillHminusDirichlet_free_L1 (n : ℕ+) (a : Coeff 1) :
    (fderiv ℂ (fun q => hillHminusDirichlet q (((π:ℂ)*n)^2)) 0) (periodOneL1Inclusion a) =
      -((-1:ℂ)^(n:ℕ)/(2*((π:ℂ)*n)^2))*hillFreeDirichletGradient n (periodOneL1Inclusion a) := by
  rw [fderiv_hillHminusDirichlet_L1,fderiv_classicalHillDirichlet_free_fourier,
    hillFreeDirichletGradient_apply]
  simp only [periodOneL1Inclusion_apply]
  have hi : (∫ t in (0:ℝ)..1, extend (periodOneL1PotentialCurve a) t*sin (π*n*(t:ℂ))^2) =
      ∫ t in (0:ℝ)..1, periodOneSynthesis a t*sin (π*n*(t:ℂ))^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hti : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
    dsimp only
    rw [extend_coe (periodOneL1PotentialCurve a) ⟨t,hti⟩,periodOneL1PotentialCurve_apply]
  rw [hi]
  have ht := integral_periodOneSynthesis_sin_sq a (n:ℤ)
  simp only [Int.cast_natCast] at ht
  rw [← ht]
  ring

theorem fderiv_hillHminusDirichlet_free (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (fun q => hillHminusDirichlet q (((π:ℂ)*n)^2)) 0) h =
      -((-1:ℂ)^(n:ℕ)/(2*((π:ℂ)*n)^2))*hillFreeDirichletGradient n h := by
  have he := denseRange_periodOneL1Inclusion.equalizer
    (fderiv ℂ (fun q => hillHminusDirichlet q (((π:ℂ)*n)^2)) 0).continuous
    ((hillFreeDirichletGradient n).continuous.const_mul (-((-1:ℂ)^(n:ℕ)/(2*((π:ℂ)*n)^2))))
    (funext (fderiv_hillHminusDirichlet_free_L1 n))
  exact congrFun he h

theorem fderiv_hillHminusCanonicalDirichlet_zero (n : ℕ+) :
    fderiv ℂ (hillHminusCanonicalDirichlet n) 0 = hillFreeDirichletGradient n := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDirichlet t.2 t.1
  have hF := (analyticOnNhd_hillHminusDirichlet_joint (hillHminusCanonicalDirichlet n 0,0) (mem_univ _)).differentiableAt
  have hs := (analyticOnNhd_hillHminusCanonicalDirichlet n 0 h0).differentiableAt
  have hzero : ∀ᶠ q in 𝓝 (0 : PeriodOneHminusOne), F (hillHminusCanonicalDirichlet n q,q)=0 := by
    filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds h0] with q hq
    exact hillHminusCanonicalDirichlet_is_root n q hq
  have hd : (fderiv ℂ F (hillHminusCanonicalDirichlet n 0,0)) (1,0) =
      (-1:ℂ)^(n:ℕ)/(2*((π:ℂ)*n)^2) := by
    rw [← deriv_spectral_section_eq_fderiv F _ 0 hF]
    change deriv (hillHminusDirichlet 0) (hillHminusCanonicalDirichlet n 0) = _
    rw [hillHminusCanonicalDirichlet_zero_eq_sq,(hasDerivAt_hillHminusDirichlet_free_eigenvalue n).deriv]
  have hne : (-1:ℂ)^(n:ℕ)/(2*((π:ℂ)*n)^2) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero (by norm_num) (pow_ne_zero _
        (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))))
  apply ContinuousLinearMap.ext
  intro h
  have hb := implicitScalarRoot_fderiv_apply F (hillHminusCanonicalDirichlet n) 0 h hF hs hzero (by rw [hd]; exact hne)
  change (fderiv ℂ (hillHminusCanonicalDirichlet n) 0) h =
    -(fderiv ℂ (fun q => hillHminusDirichlet q (hillHminusCanonicalDirichlet n 0)) 0) h / _ at hb
  rw [hd,hillHminusCanonicalDirichlet_zero_eq_sq,fderiv_hillHminusDirichlet_free] at hb
  rw [hb]
  field_simp [hne]

end NLS.KdV
