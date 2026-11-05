import NLS.KdV.ClassicalLocalPrimitive
import NLS.ZakharovShabat.ContinuousPotentialL2Bound
import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.PeriodicEndpointRootCounts

/-! # The actual Hill trace inside the existing complex ZS spectral theory

The coefficient potential here is the established physical Fourier image
of the literal interval pair (-1,-q). No new spectral operator is defined.
The exact classical/L2/canonical trace comparisons identify the actual
Hill radicand with this constructed periodic spectrum at lambda=z^2.
No real-type restriction on the complex ZS pair is imposed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- Period-one Fourier realization of the actual constant-upper pair. -/
def classicalHillCoefficientPotential (q : NLS.LinearVolterra.Curve ℂ) : PairSpace 2 :=
  periodOnePotential (sourcePhysicalL2Equiv.symm (continuousPotentialL2CLM (constantUpperPotential q)))

theorem continuous_classicalHillCoefficientPotential : Continuous classicalHillCoefficientPotential :=
  (periodOnePotential (p := 2)).continuous.comp (sourcePhysicalL2Equiv.symm.continuous.comp
    (continuousPotentialL2CLM.continuous.comp analyticOnNhd_constantUpperPotential.continuous))

theorem analyticOnNhd_classicalHillCoefficientPotential :
    AnalyticOnNhd ℂ classicalHillCoefficientPotential univ := by
  intro q _
  have hclass := (continuousPotentialL2CLM.analyticAt (constantUpperPotential q)).comp
    (analyticOnNhd_constantUpperPotential q (mem_univ _))
  have hsource := (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt _).comp hclass
  exact ((periodOnePotential (p := 2)).analyticAt _).comp hsource

theorem classicalHillCoefficientPotential_even (q : NLS.LinearVolterra.Curve ℂ) :
    classicalHillCoefficientPotential q ∈ pairParitySubspace 0 := periodOnePotential_mem _

/-- The existing canonical discriminant is the actual scalar Hill trace. -/
theorem canonicalDiscriminant_classicalHillCoefficientPotential
    (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q) z =
      classicalDiscriminant (constantUpperPotential q) z := by
  rw [classicalHillCoefficientPotential,canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm,
    continuousPotentialL2CLM_apply,l2Discriminant_of_continuous]

/-- The actual radicand vanishes precisely at the existing periodic ZS
spectrum. This is a proved physical comparison, not assumed spectral data. -/
theorem classicalHillRadicand_sq_eq_zero_iff_periodicSpectrum
    (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    classicalHillRadicand (z^2,q) = 0 ↔
      z ∈ periodicSpectrum (by simp) (classicalHillCoefficientPotential q) := by
  change classicalHillDiscriminant q (z^2)^2-4 = 0 ↔ _
  rw [sub_eq_zero,classicalHillDiscriminant_sq,
    ← canonicalDiscriminant_classicalHillCoefficientPotential]
  exact canonicalDiscriminant_sq_eq_four_iff _ (classicalHillCoefficientPotential_even q) z

/-- The frequency pullback has exactly the original spectral algebraic
multiplicity, including double zeros. -/
theorem analyticOrderNatAt_classicalHillRadicand_sq (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    analyticOrderNatAt (fun w : ℂ => classicalHillRadicand (w^2,q)) z =
      periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) z := by
  have he : (fun w : ℂ => classicalHillRadicand (w^2,q)) =
      canonicalPeriodicProduct (by simp) (classicalHillCoefficientPotential q) := by
    funext w
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four _ (classicalHillCoefficientPotential_even q),
      canonicalDiscriminant_classicalHillCoefficientPotential]
    simp only [classicalHillRadicand,classicalHillDiscriminant_sq]
  rw [he]
  exact analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num) _ z

/-- Squaring the frequency coordinate preserves the analytic order at
every nonzero frequency. -/
theorem analyticOrderNatAt_classicalHillRadicand_energy (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (hz : z ≠ 0) :
    analyticOrderNatAt (fun lam : ℂ => classicalHillRadicand (lam,q)) (z^2) =
      periodicAlgebraicMultiplicity (by simp) (classicalHillCoefficientPotential q) z := by
  have hd : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hg : AnalyticAt ℂ (fun w : ℂ => w^2) z := analyticAt_id.pow 2
  have hdn : deriv (fun w : ℂ => w^2) z ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (by norm_num) hz
  have he := analyticOrderAt_comp_of_deriv_ne_zero (f := fun lam : ℂ => classicalHillRadicand (lam,q))
    hg hdn
  have hn := congrArg ENat.toNat he
  change analyticOrderNatAt (fun w : ℂ => classicalHillRadicand (w^2,q)) z =
    analyticOrderNatAt (fun lam : ℂ => classicalHillRadicand (lam,q)) (z^2) at hn
  rw [← hn]
  exact analyticOrderNatAt_classicalHillRadicand_sq q z

end NLS.KdV
