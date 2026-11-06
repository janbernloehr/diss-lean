import NLS.SequenceSpaces.PeriodOneMiuraCompactJacobian
import NLS.FunctionalAnalysis.CompactRightInverseBetweenSpaces

/-! # Compact remainders of actual native Miura inverse derivatives

The free mass equivalence is constructed from the already verified actual
zero-coefficient Jacobian. Every supplied analytic right inverse has the
same principal inverse, even if its nonlinear Jacobian is not assumed
injective. Both shifted and unshifted Riccati equations are covered.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- The exact native free mass equivalence H^t-to-H^(t-1). -/
def periodOneSobolevFreeMassEquiv (m : ℕ) (t : ℝ) (ht : 0≤t) :
    WeightedCoeff (Weight.sobolev t) 2 ≃L[ℂ] WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  periodOneSobolevMiuraJacobianEquiv m t ht 0 (by
    simpa only [map_zero] using bijective_periodOneMiuraJacobian_of_small m 0 (by simp))

@[simp] theorem periodOneSobolevFreeMassEquiv_apply (m : ℕ) (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    periodOneSobolevFreeMassEquiv m t ht a=periodOneSobolevMassOperator m t a := by
  change periodOneSobolevMiuraJacobian m t ht 0 a=_
  apply Subtype.ext
  funext n
  simp only [periodOneSobolevMiuraJacobian_apply,WeightedCoeff.zero_val,zero_mul,tsum_zero,
    mul_zero,add_zero,periodOneSobolevMassOperator_apply]

theorem periodOneSobolevFreeMassEquiv_clm (m : ℕ) (t : ℝ) (ht : 0≤t) :
    (periodOneSobolevFreeMassEquiv m t ht).toContinuousLinearMap=periodOneSobolevMassOperator m t := by
  ext a
  exact periodOneSobolevFreeMassEquiv_apply m t ht a

/-- The actual unshifted native Miura map u'+u², including its central mode. -/
def periodOneSobolevMiura (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev t) 2) : WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  periodOneSobolevShiftedMiura 0 t ht a-
    WeightedCoeff.sobolevInclusion (by linarith : t-1≤t) a

/-- Native unshifted Miura and the original distributional map have the
SAME raw coefficients, at every complex source and every index. -/
theorem periodOneSobolevMiura_apply_toL2 (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (periodOneSobolevMiura t ht a).val n=
      (periodOneMiura (WeightedCoeff.sobolevToL2 ht a)).val n := by
  simp only [periodOneSobolevMiura,WeightedCoeff.sub_val,periodOneSobolevShiftedMiura_apply,
    WeightedCoeff.sobolevInclusion_apply,periodOneMiura_apply,WeightedCoeff.sobolevToL2_apply,
    periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
  ring

/-- The exact native unshifted Jacobian, with no amplitude approximation. -/
def periodOneSobolevUnshiftedMiuraJacobian (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  periodOneSobolevMiuraJacobian 0 t ht a-
    WeightedCoeff.sobolevInclusion (by linarith : t-1≤t)

theorem hasFDerivAt_periodOneSobolevMiura (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    HasFDerivAt (periodOneSobolevMiura t ht) (periodOneSobolevUnshiftedMiuraJacobian t ht a) a :=
  (hasFDerivAt_periodOneSobolevShiftedMiura 0 t ht a).sub
    (WeightedCoeff.sobolevInclusion (by linarith : t-1≤t)).hasFDerivAt

/-- The actual unshifted Jacobian is a compact perturbation of the free
mass equivalence at every complex native coefficient and EVERY t>=0. -/
theorem isCompactOperator_periodOneSobolevUnshiftedMiuraJacobian_sub_free
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2) :
    IsCompactOperator (periodOneSobolevUnshiftedMiuraJacobian t ht a-
      (periodOneSobolevFreeMassEquiv 0 t ht).toContinuousLinearMap) := by
  rw [periodOneSobolevFreeMassEquiv_clm]
  have he : periodOneSobolevUnshiftedMiuraJacobian t ht a-periodOneSobolevMassOperator 0 t=
      (periodOneSobolevMiuraJacobian 0 t ht a-periodOneSobolevMassOperator 0 t)-
        WeightedCoeff.sobolevInclusion (by linarith : t-1≤t) := by
    unfold periodOneSobolevUnshiftedMiuraJacobian
    abel
  rw [he]
  exact (isCompactOperator_periodOneSobolevMiuraJacobian_sub_mass 0 t ht a).sub
    (isCompactOperator_sobolevInclusion_sub_one t)

/-- A supplied ACTUAL native analytic inverse germ of the shifted Miura
equation has free inverse principal part and compact derivative remainder. -/
theorem isCompactOperator_fderiv_shiftedMiura_rightInverse_sub_free
    (m : ℕ) (t : ℝ) (ht : 0≤t)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (hg : DifferentiableAt ℂ g q)
    (he : (fun p => periodOneSobolevShiftedMiura m t ht (g p)) =ᶠ[𝓝 q] id) :
    IsCompactOperator (fderiv ℂ g q-(periodOneSobolevFreeMassEquiv m t ht).symm.toContinuousLinearMap) := by
  have hright : (periodOneSobolevMiuraJacobian m t ht (g q)).comp (fderiv ℂ g q)=
      ContinuousLinearMap.id ℂ (WeightedCoeff (Weight.sobolev (t-1)) 2) :=
    (((hasFDerivAt_periodOneSobolevShiftedMiura m t ht (g q)).comp q hg.hasFDerivAt).congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id q)
  apply isCompactOperator_rightInverse_sub_equiv_symm _ _ (periodOneSobolevFreeMassEquiv m t ht) _ hright
  rw [periodOneSobolevFreeMassEquiv_clm]
  exact isCompactOperator_periodOneSobolevMiuraJacobian_sub_mass m t ht (g q)

/-- A supplied ACTUAL native analytic inverse of the unshifted Riccati
map, with any fixed energy translation, has the SAME free principal inverse.
This statement does not assume bijectivity of its nonlinear Jacobian. -/
theorem isCompactOperator_fderiv_unshiftedMiura_rightInverse_sub_free
    (t : ℝ) (ht : 0≤t)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2)
    (q k : WeightedCoeff (Weight.sobolev (t-1)) 2) (hg : DifferentiableAt ℂ g q)
    (he : (fun p => periodOneSobolevMiura t ht (g p)) =ᶠ[𝓝 q] (fun p => p+k)) :
    IsCompactOperator (fderiv ℂ g q-(periodOneSobolevFreeMassEquiv 0 t ht).symm.toContinuousLinearMap) := by
  have hright : (periodOneSobolevUnshiftedMiuraJacobian t ht (g q)).comp (fderiv ℂ g q)=
      ContinuousLinearMap.id ℂ (WeightedCoeff (Weight.sobolev (t-1)) 2) :=
    (((hasFDerivAt_periodOneSobolevMiura t ht (g q)).comp q hg.hasFDerivAt).congr_of_eventuallyEq he.symm).unique ((hasFDerivAt_id q).add_const k)
  exact isCompactOperator_rightInverse_sub_equiv_symm _ _ (periodOneSobolevFreeMassEquiv 0 t ht)
    (isCompactOperator_periodOneSobolevUnshiftedMiuraJacobian_sub_free t ht (g q)) hright

end NLS
