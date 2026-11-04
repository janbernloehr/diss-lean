import NLS.KdV.HillNativeDirichletFirstVariation
import NLS.ComplexAnalysis.MovingSpectralParameter
import NLS.FunctionalAnalysis.LinearSourceRestrictionDerivative

/-! Exact ACTUAL canonical Dirichlet norming derivative at the origin.
The moving energy contribution vanishes by the independently proved free
terminal energy derivative. Density gives every complex native direction. -/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
open scoped Real ENNReal
namespace NLS.KdV

def hillFreeNormingGradient (n : ℕ+) : PeriodOneHminusOne →L[ℂ] ℂ :=
  ((-1:ℂ)^(n:ℕ)/(4*I*((π:ℂ)*n))) •
    (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 (-(n:ℤ))-
      WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 (n:ℤ))

theorem hillFreeNormingGradient_apply (n : ℕ+) (h : PeriodOneHminusOne) :
    hillFreeNormingGradient n h =
      ((-1:ℂ)^(n:ℕ)/(4*I*((π:ℂ)*n)))*(h.val (-(n:ℤ))-h.val (n:ℤ)) := by
  simp only [hillFreeNormingGradient,smul_apply,sub_apply,WeightedCoeff.evalCLM_apply,smul_eq_mul]

def hillL1TerminalFamily (p : ℂ × Coeff 1) : ℂ :=
  hillL2DirichletTerminal (periodOneL1PhysicalCoefficients p.2) p.1

def hillL1CanonicalDirichlet (n : ℕ+) (a : Coeff 1) : ℂ :=
  hillHminusCanonicalDirichlet n (periodOneL1Inclusion a)

theorem analyticOnNhd_hillL1TerminalFamily : AnalyticOnNhd ℂ hillL1TerminalFamily univ := by
  intro p _
  have hD : AnalyticAt ℂ (fun q : ℂ × Coeff 1 => periodOneL1PhysicalCoefficients q.2) p :=
    (_root_.ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Coeff 1) (F := Coeff 2)
      periodOneL1PhysicalCoefficients p.2).comp
        (f := fun q : ℂ × Coeff 1 => q.2) analyticAt_snd
  exact (analyticOnNhd_hillL2DirichletTerminal_joint
    (p.1,periodOneL1PhysicalCoefficients p.2) (mem_univ _)).comp
      (f := fun q : ℂ × Coeff 1 => (q.1,periodOneL1PhysicalCoefficients q.2))
      (analyticAt_fst.prod hD)

theorem hillL1TerminalFamily_eq_classical (μ : ℂ) (a : Coeff 1) :
    hillL1TerminalFamily (μ,a) = classicalHillDirichletTerminal (periodOneL1PotentialCurve a) μ :=
  hillL2DirichletTerminal_periodOneL1_eq_classical a μ

theorem hillL1TerminalFamily_zero_eq_classical (μ : ℂ) :
    hillL1TerminalFamily (μ,0) = classicalHillDirichletTerminal 0 μ := by
  rw [hillL1TerminalFamily_eq_classical,map_zero]

theorem hillL1CanonicalDirichlet_zero (n : ℕ+) :
    hillL1CanonicalDirichlet n 0 = ((π:ℂ)*n)^2 := by
  rw [hillL1CanonicalDirichlet,map_zero,hillHminusCanonicalDirichlet_zero_eq_sq]

theorem fderiv_hillL1MovingTerminal_zero (n : ℕ+) :
    fderiv ℂ (fun a => hillL1TerminalFamily (hillL1CanonicalDirichlet n a,a)) 0 =
      fderiv ℂ (fun a => hillL1TerminalFamily (((π:ℂ)*n)^2,a)) 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  have hsN : DifferentiableAt ℂ (hillHminusCanonicalDirichlet n) (periodOneL1Inclusion 0) := by
    simpa only [map_zero] using (analyticOnNhd_hillHminusCanonicalDirichlet n 0 h0).differentiableAt
  have hs : DifferentiableAt ℂ (hillL1CanonicalDirichlet n) 0 :=
    hsN.comp 0 periodOneL1Inclusion.differentiableAt
  have hF := (analyticOnNhd_hillL1TerminalFamily (hillL1CanonicalDirichlet n 0,0) (mem_univ _)).differentiableAt
  have hde : deriv (fun z => hillL1TerminalFamily (z,0)) (hillL1CanonicalDirichlet n 0) = 0 := by
    have he : (fun z => hillL1TerminalFamily (z,0)) = classicalHillDirichletTerminal 0 :=
      funext hillL1TerminalFamily_zero_eq_classical
    rw [he,hillL1CanonicalDirichlet_zero,(hasDerivAt_classicalHillDirichletTerminal_free_eigenvalue n).deriv]
  have hmove := fderiv_moving_spectral_parameter hillL1TerminalFamily (hillL1CanonicalDirichlet n) 0 hF hs
  have hz : (0:ℂ) • (fderiv ℂ (hillL1CanonicalDirichlet n) 0) = 0 := by
    ext b
    change (0:ℂ)*((fderiv ℂ (hillL1CanonicalDirichlet n) 0) b)=0
    exact zero_mul _
  rw [hde,hz,add_zero] at hmove
  simpa only [hillL1CanonicalDirichlet_zero] using hmove

theorem fderiv_hillL1TerminalFamily_source_zero (n : ℕ+) :
    fderiv ℂ (fun a => hillL1TerminalFamily (((π:ℂ)*n)^2,a)) 0 =
      (fderiv ℂ (fun Q => classicalHillDirichletTerminal Q (((π:ℂ)*n)^2)) 0).comp
        periodOneL1PotentialCurve := by
  have he : (fun a => hillL1TerminalFamily (((π:ℂ)*n)^2,a)) =
      fun a => classicalHillDirichletTerminal (periodOneL1PotentialCurve a) (((π:ℂ)*n)^2) :=
    funext (hillL1TerminalFamily_eq_classical (((π:ℂ)*n)^2))
  rw [he]
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hP : DifferentiableAt ℂ (fun Q => classicalHillDirichletTerminal Q (((π:ℂ)*n)^2)) 0 :=
    (analyticAt_snd.comp (analyticOnNhd_classicalHillFlow_potential _ (0,1) t 0 (mem_univ _))).differentiableAt
  have hPi : HasFDerivAt (fun Q => classicalHillDirichletTerminal Q (((π:ℂ)*n)^2))
      (fderiv ℂ (fun Q => classicalHillDirichletTerminal Q (((π:ℂ)*n)^2)) 0)
      (periodOneL1PotentialCurve 0) := by simpa only [map_zero] using hP.hasFDerivAt
  exact (hPi.comp 0 periodOneL1PotentialCurve.hasFDerivAt).fderiv

theorem hillHminusDirichletNorming_L1_eq (n : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    hillHminusDirichletNorming n (periodOneL1Inclusion a) =
      hillL1TerminalFamily (hillL1CanonicalDirichlet n a,a) := by
  rw [hillL1TerminalFamily_eq_classical]
  exact hillHminusDirichletNorming_eq_classical_L1 n a ha

theorem hillHminusDirichletNorming_L1_eventually_eq (n : ℕ+) :
    (fun b => hillHminusDirichletNorming n (periodOneL1Inclusion b)) =ᶠ[𝓝 0]
      fun b => hillL1TerminalFamily (hillL1CanonicalDirichlet n b,b) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  exact (NLS.FunctionalAnalysis.eventually_comp_linear_zero periodOneL1Inclusion
    hillHminusCanonicalDirichletDomain isOpen_hillHminusCanonicalDirichletDomain h0).mono
      (fun b hb => hillHminusDirichletNorming_L1_eq n b hb)

theorem fderiv_hillHminusDirichletNorming_L1 (n : ℕ+) (a : Coeff 1) :
    (fderiv ℂ (hillHminusDirichletNorming n) 0) (periodOneL1Inclusion a) =
      (fderiv ℂ (fun Q => classicalHillDirichletTerminal Q (((π:ℂ)*n)^2)) 0)
        (periodOneL1PotentialCurve a) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  have hN := (analyticOnNhd_hillHminusDirichletNorming n 0 h0).differentiableAt
  have hNc := NLS.FunctionalAnalysis.fderiv_comp_linear_zero
    (hillHminusDirichletNorming n) periodOneL1Inclusion hN
  calc
    _ = (fderiv ℂ (fun b => hillHminusDirichletNorming n (periodOneL1Inclusion b)) 0) a :=
      congrArg (fun L : Coeff 1 →L[ℂ] ℂ => L a) hNc.symm
    _ = (fderiv ℂ (fun b => hillL1TerminalFamily (hillL1CanonicalDirichlet n b,b)) 0) a :=
      congrArg (fun L : Coeff 1 →L[ℂ] ℂ => L a)
        (hillHminusDirichletNorming_L1_eventually_eq n).fderiv_eq
    _ = _ := by
      rw [fderiv_hillL1MovingTerminal_zero,fderiv_hillL1TerminalFamily_source_zero,
        ContinuousLinearMap.comp_apply]

theorem fderiv_hillHminusDirichletNorming_free_L1 (n : ℕ+) (a : Coeff 1) :
    (fderiv ℂ (hillHminusDirichletNorming n) 0) (periodOneL1Inclusion a) =
      hillFreeNormingGradient n (periodOneL1Inclusion a) := by
  rw [fderiv_hillHminusDirichletNorming_L1,fderiv_classicalHillDirichletTerminal_free_fourier,
    hillFreeNormingGradient_apply]
  simp only [periodOneL1Inclusion_apply]
  have hi : (∫ t in (0:ℝ)..1, extend (periodOneL1PotentialCurve a) t*sin (2*(π*n)*(t:ℂ))) =
      ∫ t in (0:ℝ)..1, periodOneSynthesis a t*sin (2*(π*n)*(t:ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hti : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
    dsimp only
    rw [extend_coe (periodOneL1PotentialCurve a) ⟨t,hti⟩,periodOneL1PotentialCurve_apply]
  rw [hi]
  have ht := integral_periodOneSynthesis_sin a (n:ℤ)
  simp only [Int.cast_natCast] at ht
  rw [show 2*((π:ℂ)*n) = 2*π*n by ring,ht]
  ring

theorem fderiv_hillHminusDirichletNorming_zero (n : ℕ+) :
    fderiv ℂ (hillHminusDirichletNorming n) 0 = hillFreeNormingGradient n := by
  have he := denseRange_periodOneL1Inclusion.equalizer
    (fderiv ℂ (hillHminusDirichletNorming n) 0).continuous (hillFreeNormingGradient n).continuous
    (funext (fderiv_hillHminusDirichletNorming_free_L1 n))
  exact DFunLike.ext' he

end NLS.KdV
