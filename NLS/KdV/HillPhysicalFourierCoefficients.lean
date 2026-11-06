import NLS.KdV.HillStateSecondDerivative
import NLS.KdV.HillDirichletPotentialDerivative
import NLS.Fourier.CircleUnitCoefficients

/-! # Original physical Hill fields have the native unit Fourier coefficients

The first-order Hill realization and its actual variations retain the
minus sign in their lower component. The physical scalar potential has
exactly the halved even coefficients, with no additional period factor.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillIntervalPotential_eq_circlePullback_ae (q : Coeff 2) :
    hillIntervalPotential q =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] circlePullback (l2Synthesis q) := by
  have hn := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circle_ae_pullback (Lp.coeFn_neg (l2Synthesis q)))
  filter_upwards [physicalRestrictionL2_representative (hillFirstOrderPotential q),hn] with x hx hneg
  change -(intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) x).2 = _
  rw [hx]
  change -circlePullback (l2Synthesis (-q)) x = _
  rw [map_neg]
  change circlePullback (-l2Synthesis q) x = -circlePullback (l2Synthesis q) x at hneg
  rw [hneg,neg_neg]

theorem hillPhysicalDirection_eq_circlePullback_ae (h : Coeff 2) :
    (fun x => -(hillPhysicalDirection h).ofLp.2 x)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] circlePullback (l2Synthesis h) := by
  have hn := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circle_ae_pullback (Lp.coeFn_neg (l2Synthesis h)))
  have hr := physicalRestrictionL2_representative (hillFirstOrderDirection h)
  change intervalL2Representative (hillPhysicalDirection h)
    =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] physicalBase (hillFirstOrderDirection h) at hr
  filter_upwards [hr,hn] with x hx hneg
  change -(intervalL2Representative (hillPhysicalDirection h) x).2 = _
  rw [hx]
  change -circlePullback (l2Synthesis (-h)) x = _
  rw [map_neg]
  change circlePullback (-l2Synthesis h) x = -circlePullback (l2Synthesis h) x at hneg
  rw [hneg,neg_neg]

theorem periodOneCoefficient_circlePullback_periodDouble (q : Coeff 2) (n : ℤ) :
    periodOneCoefficient (circlePullback (l2Synthesis (Coeff.periodDouble q))) n = q n := by
  rw [← circleUnitCoefficients_apply]
  change periodTwoToUnit (by norm_num) (by simp) (l2Synthesis.symm (l2Synthesis (Coeff.periodDouble q))) n = _
  rw [LinearIsometryEquiv.symm_apply_apply,periodTwoToUnit_periodDouble]

theorem periodOneCoefficient_hillIntervalPotential_periodDouble (q : Coeff 2) (n : ℤ) :
    periodOneCoefficient (hillIntervalPotential (Coeff.periodDouble q)) n = q n := by
  rw [periodOneCoefficient]
  rw [fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1)
    (hillIntervalPotential_eq_circlePullback_ae (Coeff.periodDouble q))]
  exact periodOneCoefficient_circlePullback_periodDouble q n

theorem periodOneCoefficient_hillIntervalPotential (q : Coeff 2)
    (hq : q ∈ Coeff.paritySubspace 0) (n : ℤ) :
    periodOneCoefficient (hillIntervalPotential q) n = Coeff.periodHalve q n := by
  have he : Coeff.periodDouble (Coeff.periodHalve q) = q :=
    (Coeff.periodDouble_periodHalve q).trans ((Coeff.parityProjection_eq_self_iff 0 q).mpr hq)
  conv_lhs => rw [← he]
  exact periodOneCoefficient_hillIntervalPotential_periodDouble _ n

theorem periodOneCoefficient_hillPhysicalDirection_periodDouble (h : Coeff 2) (n : ℤ) :
    periodOneCoefficient (fun x => -(hillPhysicalDirection (Coeff.periodDouble h)).ofLp.2 x) n = h n := by
  rw [periodOneCoefficient]
  rw [fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1)
    (hillPhysicalDirection_eq_circlePullback_ae (Coeff.periodDouble h))]
  exact periodOneCoefficient_circlePullback_periodDouble h n

end NLS.KdV
