import NLS.KdV.SingularDirichletOperatorDomain
import NLS.KdV.UnitHillMassDensity
import NLS.KdV.SingularDirichletFreeIsomorphism

/-! # Dense domain of the actual native Dirichlet partial operator

The full dual is reached densely by unit-period mass forms with zero trace.
Restriction to zero-trace tests is surjective, and these restricted mass
forms are exactly the unchanged native domain inclusion.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
open NLS.Fourier.SmoothPeriodicTest NLS.ZakharovShabat
local instance dirichletDenseDomainH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletDenseDomainH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- The full mass form is exactly the original distributional inclusion,
tested on all unit-period H1 vectors before any trace restriction. -/
theorem unitHillMassDual_eq_originalMass (f : ScalarDomain 2) :
    unitHillMassDual f =
      (sobolevDualIsometry 1 (by norm_num)
        (singularHillDomainInclusion (unitSobolevOriginalH1 f))).comp unitSobolevOriginalH1 := by
  apply scalarMode_dual_ext
  intro n
  change WeightedCoeff.sobolevBilinearPairing 1 (scalarMode n 1) (unitHillMass f) =
    singularHillPairing (singularHillDomainInclusion (unitSobolevOriginalH1 f))
      (unitSobolevOriginalH1 (scalarMode n 1))
  rw [WeightedCoeff.sobolevBilinearPairing_apply]
  simp only [scalarMode_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq,
    unitHillMass_coefficient]
  rw [singularHillPairing, sobolevDualIsometry_apply]
  have hm (k : ℤ) : (unitSobolevOriginalH1 (scalarMode n 1)).val (mode (-k)) =
      if k = 2*n then 1 else 0 := by
    rw [unitSobolevOriginalH1_coefficient]
    change (Coeff.periodDoubleSobolev (scalarMode n 1)).val k = _
    rw [Coeff.periodDoubleSobolev_scalarMode, scalarMode_apply]
  simp only [hm, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  rw [show 2*n = -(2*(-n)) by ring, singularHillDomainInclusion_coefficient,
    unitSobolevOriginalH1_coefficient, Coeff.periodDouble_even, scalarInclusion_apply]

/-- The restricted mass form is the actual native inclusion on every H1 vector. -/
theorem singularDirichletDomainInclusion_eq_restricted_mass :
    singularDirichletDomainInclusion = unitDirichletDualRestriction.comp
      (unitHillMassDual.comp unitDirichletSubspace.subtypeL) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro g
  change singularHillPairing (singularHillDomainInclusion (unitDirichletOriginalH1 f))
    (unitDirichletOriginalH1 g) = unitHillMassDual f.val g.val
  rw [unitHillMassDual_eq_originalMass]
  rfl

/-- The complete original zero-trace H1 domain is dense in its full H-minus-one base. -/
theorem denseRange_singularDirichletDomainInclusion : DenseRange singularDirichletDomainInclusion := by
  rw [singularDirichletDomainInclusion_eq_restricted_mass]
  exact unitDirichletDualRestriction_surjective.denseRange.comp
    denseRange_unitHillMassDual_on_Dirichlet unitDirichletDualRestriction.continuous

/-- Dense domain in the actual partial-operator API, with no smaller base or domain. -/
theorem dense_domain_singularDirichletPartialOperator
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    Dense ((singularDirichletPartialOperator q).domain : Set UnitDirichletHminus) :=
  denseRange_singularDirichletDomainInclusion

end NLS.KdV
