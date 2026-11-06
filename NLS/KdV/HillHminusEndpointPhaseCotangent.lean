import NLS.KdV.HillHminusPhysicalGermCotangent
import NLS.KdV.HillFullEndpointNativeCotangent
import NLS.KdV.HillPhaseLocalSign
import NLS.KdV.HillSpectralCartesianTerminal

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The full physical phase has the original terminal-angle exponential,
including its minus-pi anchor and COMPLETE scalar correction sum. -/
theorem hillOriginalFullPhaseFactor_eq_exp_of_terminal
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (θ : ℂ) (hθ : θ.im = 0)
    (hpoint : NLS.ComplexAnalysis.cosineGapPoint
      (hillRealGapCenter q.val q.property.1 q.property.2 n)
      (hillRealGapHalfLength q.val q.property.1 q.property.2 n) θ =
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos : ℂ))
    (hsin : Complex.sin θ = hillDirichletGapSine q.val q.property.1 q.property.2 n n.pos) :
    hillOriginalFullPhaseFactor n q = Complex.exp (I *
      (hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos + θ - Real.pi)) := by
  have he : θ = (θ.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using hθ
  have hc := hillDirichletCirclePhase_eq_exp_of_terminal q.val q.property.1 q.property.2
    n n.pos hgap θ.re (by simpa only [←he] using hpoint) (by simpa only [←he] using hsin)
  rw [hillOriginalFullPhaseFactor,hc,←Complex.exp_add]
  congr 1
  rw [←he]
  ring

/-- At an all-periodic original source, EVERY physically matched analytic
H-minus-one full-phase germ has the exact convergent physical norming-span
cotangent. The actual multiplicative phase and its sign are retained. -/
theorem exists_hillOriginalFullPhase_hminus_endpoint_cotangent
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1 ≤ k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk = 0)
    (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillOriginalFullPhaseFactor n p) :
    ∃ c : ℕ → ℂ, ∃ a : WeightedCoeff (Weight.sobolev 1) 2,
      Summable (fun j => ‖c j‖) ∧
      (∀ k : ℤ, a.val k = Fourier.unitFourierCoefficient
        (NLS.LinearVolterra.extend (hillInfiniteNormingGradient q c)) k) ∧
      NLS.Poisson.hminusScalarGradient F (hillOriginalHminusSource q.val) =
        (I * hillOriginalFullPhaseFactor n q) • a ∧
      ∀ d : ℕ → ℂ, ∀ hd : Summable (fun j => ‖d j‖),
        NLS.Poisson.gardnerBivector a
          (hillInfiniteNormingUnitCotangent (by simp) (by simp [IsRealHillPotential]) q d hd) = 0 := by
  obtain ⟨Θ,ε,c,a,hΘ,_,hphysical,hc,hcoeff,hD,hzero⟩ :=
    exists_hillFullPhysicalPhase_endpoint_native_cotangent
      (by simp) (by simp [IsRealHillPotential]) q n n.pos hgap hterminal
  let G : Coeff 2 → ℂ := fun p => Complex.exp (I * Θ p)
  have hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val) :=
    (analyticAt_const.mul hΘ).cexp'
  have hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val) = hillOriginalFullPhaseFactor n p := by
    filter_upwards [hphysical] with p hp
    dsimp only [G]
    rw [hp.2.2.2.2]
    exact (hillOriginalFullPhaseFactor_eq_exp_of_terminal p n hp.1
      (ε (SpectralWeight.one.toCoeff p.val)) hp.2.1 hp.2.2.1 hp.2.2.2.1).symm
  have hFG : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = G (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hGM] with p hp hpg
    exact hp.trans hpg.symm
  have hdG := (hΘ.differentiableAt.hasFDerivAt.const_mul I).cexp
  have hrestrict : (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)).comp hillNativeHilbertDirection =
      (WeightedCoeff.sobolevBilinearPairing 1
        ((I * hillOriginalFullPhaseFactor n q) • a)).comp NLS.Poisson.hilbertToHminus := by
    rw [hdG.fderiv]
    ext v
    have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L v) hD
    simp only [ContinuousLinearMap.comp_apply] at he
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      smul_eq_mul,map_smul]
    rw [he,show Complex.exp (I * Θ (SpectralWeight.one.toCoeff q.val)) =
      hillOriginalFullPhaseFactor n q from hGM.self_of_nhds]
    ring
  exact ⟨c,a,hc,hcoeff,
    hillHminusPhysicalGerm_gradient_eq_of_native_restriction q F G hF hG hFG _ hrestrict,hzero⟩

end NLS.KdV
