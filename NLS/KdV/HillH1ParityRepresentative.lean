import NLS.KdV.SingularHillPhysicalParity
import NLS.Fourier.SobolevParitySynthesis
import NLS.Fourier.UnitIntervalDirichletIdentification
import NLS.Fourier.UnitDirichletL2

/-! Faithful physical representatives and interval restriction of original
parity H1 vectors, with exact source periodic/unit-interval normalization. -/
noncomputable section
open Set MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- Physical L2 parity implies the SAME support property for every raw
coefficient of the ENTIRE original H1 distribution. -/
theorem hillH1_coefficients_of_physical_parity (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : circleL2ParityProjection r (singularHillL2DomainInclusion f)=singularHillL2DomainInclusion f) :
    ∀ k : ℤ, k%2 ≠ r%2 → f.val (mode (-k))=0 := by
  have he : periodicParityProjection 1 2 r f=f := singularHillL2DomainInclusion_injective
    ((singularHillL2DomainInclusion_parity r f).trans hf)
  intro k hk
  have hc := congrArg (fun g : FourierLebesgueSpace (2:ℝ) 1 2 => g.val (mode (-k))) he
  rw [periodicParityProjection_coefficient,if_neg hk] at hc
  exact hc.symm

/-- The IDENTICAL actual continuous H1 representative satisfies physical
period-one/antiperiod-one translation at EVERY real point. -/
theorem hillH1Continuous_translate_one_of_parity (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : circleL2ParityProjection r (singularHillL2DomainInclusion f)=singularHillL2DomainInclusion f) (x : ℝ) :
    singularHillContinuousDomainInclusion f ((x+1:ℝ) : AddCircle (2:ℝ))=
      wave r 1*singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ)) := by
  change sobolevSynthesis (by simp) (sobolevCoefficients 1 2 f) ((x+1:ℝ) : AddCircle (2:ℝ))=_
  exact sobolevSynthesis_translate_one_of_parity r (sobolevCoefficients 1 2 f)
    (hillH1_coefficients_of_physical_parity r f hf) x

/-- The actual unit-interval squared norm is EXACTLY the original periodic
physical L2 norm squared for either source parity. -/
theorem integral_sq_hillH1Continuous_unit_of_parity (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : circleL2ParityProjection r (singularHillL2DomainInclusion f)=singularHillL2DomainInclusion f) :
    (∫ x in (0:ℝ)..1, ‖singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ))‖^2)=
      ‖singularHillL2DomainInclusion f‖^2 := by
  rw [norm_singularHillL2DomainInclusion]
  have ha : scalarInclusion (sobolevCoefficients 1 2 f)=h1L2Coefficients f := by
    ext k
    rw [scalarInclusion_apply,h1L2Coefficients_apply]
    rfl
  rw [← ha]
  change (∫ x in (0:ℝ)..1, ‖sobolevSynthesis (by simp) (sobolevCoefficients 1 2 f) (x : AddCircle (2:ℝ))‖^2)=_
  exact integral_sq_sobolevSynthesis_unit_of_parity r (sobolevCoefficients 1 2 f)
    (hillH1_coefficients_of_physical_parity r f hf)

/-- Every full original H1 vector with zero physical endpoints has a UNIQUE
representative in the ENTIRE original native Dirichlet H1 domain. -/
theorem existsUnique_hillH1_DirichletRestriction (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (h0 : singularHillContinuousDomainInclusion f (0 : AddCircle (2:ℝ))=0)
    (h1 : singularHillContinuousDomainInclusion f ((1:ℝ) : AddCircle (2:ℝ))=0) :
    ∃! g : UnitDirichletH1, ∀ x ∈ Icc (0:ℝ) 1,
      unitDirichletRepresentative g x=singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ)) := by
  let a := sobolevCoefficients 1 2 f
  have hreg : HasIntervalH1Regularity (fun x : ℝ => singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ))) := by
    constructor
    · exact (absolutelyContinuous_sobolevSynthesis a).mono
        (show uIcc (0:ℝ) 1 ⊆ uIcc 0 2 by
          simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
          exact Icc_subset_Icc le_rfl (by norm_num))
    · exact (memLp_deriv_sobolevSynthesis a).mono_measure
        (Measure.restrict_mono (Ioc_subset_Ioc le_rfl (by norm_num : (1:ℝ) ≤ 2)) le_rfl)
  exact existsUnique_unitDirichletRepresentative _ hreg h0 h1

/-- A parity H1 vector that vanishes at zero has a faithful native interval
restriction with EXACTLY the SAME physical L2 norm, not a rescaled norm. -/
theorem exists_hillH1_DirichletRestriction_norm (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : circleL2ParityProjection r (singularHillL2DomainInclusion f)=singularHillL2DomainInclusion f)
    (h0 : singularHillContinuousDomainInclusion f (0 : AddCircle (2:ℝ))=0) :
    ∃ g : UnitDirichletH1,
      (∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x=singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ))) ∧
      ‖unitDirichletL2Inclusion g‖=‖singularHillL2DomainInclusion f‖ := by
  have h1 : singularHillContinuousDomainInclusion f ((1:ℝ) : AddCircle (2:ℝ))=0 := by
    have h := hillH1Continuous_translate_one_of_parity r f hf 0
    simpa [h0] using h
  obtain ⟨g,hg,_⟩ := existsUnique_hillH1_DirichletRestriction f h0 h1
  refine ⟨g,hg,?_⟩
  have hsq : ‖unitDirichletL2Inclusion g‖^2=‖singularHillL2DomainInclusion f‖^2 := by
    rw [norm_sq_unitDirichletL2Inclusion,← integral_sq_hillH1Continuous_unit_of_parity r f hf]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hg x (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)]
  nlinarith [norm_nonneg (unitDirichletL2Inclusion g),norm_nonneg (singularHillL2DomainInclusion f)]

end NLS.KdV
