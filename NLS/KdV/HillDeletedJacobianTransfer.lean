import NLS.KdV.HillExtendedPositiveJacobian
import NLS.KdV.HillMixedSupportedPeriodMap
import NLS.SequenceSpaces.PositiveDeletedInclusion

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillMixedComplexPeriodSequence_positiveDeleted_fixed
    (N n : ℕ) (hn : 1≤n) (t : Coeff 2 × Coeff 2) :
    Coeff.positiveDeletedProjection 2 (n : ℤ) (hillMixedComplexPeriodSequence q hq hr h0q h0r N n t)=
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n t := by
  apply (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) _).mpr
  intro m hm
  exact hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn t m hm

theorem fderiv_hillMixedPeriod_positiveDeleted_fixed
    (N n : ℕ) (hn : 1≤n) (a p : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a) :
    (Coeff.positiveDeletedProjection 2 (n : ℤ)).comp
      (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a)=
      fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a := by
  have hd := (Coeff.positiveDeletedProjection 2 (n : ℤ)).hasFDerivAt.comp a hF.hasFDerivAt
  have he : (fun b : Coeff 2 => Coeff.positiveDeletedProjection 2 (n : ℤ)
      (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)))=
      (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) :=
    funext (fun b => hillMixedComplexPeriodSequence_positiveDeleted_fixed q hq hr h0q h0r N n hn (b,p))
  simp only [Function.comp_def] at hd
  rw [he] at hd
  exact hd.unique hF.hasFDerivAt

theorem fderiv_hillMixedSupportedPeriodMap_root_eq_restriction
    (N n : ℕ) (a p : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a) :
    fderiv ℂ (fun b : PositiveDeletedCoeff 2 (n : ℤ) =>
      hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0=
      (Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).comp
        ((fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a).comp
          (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL) := by
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let P := Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
  have hi : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) inc 0 :=
    inc.hasFDerivAt.const_add a
  have hG : HasFDerivAt (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p))
      (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a)
      (a+((0 : PositiveDeletedCoeff 2 (n : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using hF.hasFDerivAt
  have hd := P.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (n : ℤ))
    (hG.comp (f := fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) 0 hi)
  convert! hd.fderiv using 1

/-- The full-positive extension agrees exactly with the original
positive-deleted supported Jacobian under the natural isometric inclusion. -/
theorem hillExtendedPositivePeriodJacobian_on_positiveDeleted
    (N n : ℕ) (hn : 1≤n) (a p : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a)
    (h : PositiveDeletedCoeff 2 (n : ℤ)) :
    hillExtendedPositivePeriodJacobian q hq hr h0q h0r N n a p (Coeff.positiveDeletedToPositive 2 (n : ℤ) h)=
      Coeff.positiveDeletedToPositive 2 (n : ℤ) (fderiv ℂ (fun b : PositiveDeletedCoeff 2 (n : ℤ) =>
        hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0 h) := by
  let A := fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a
  let L := fderiv ℂ (fun b : PositiveDeletedCoeff 2 (n : ℤ) =>
    hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0
  have hfixed : Coeff.positiveDeletedProjection 2 (n : ℤ) (A (h : Coeff 2))=A (h : Coeff 2) :=
    congrArg (fun T : Coeff 2 →L[ℂ] Coeff 2 => T (h : Coeff 2))
      (fderiv_hillMixedPeriod_positiveDeleted_fixed q hq hr h0q h0r N n hn a p hF)
  have hL : (L h : Coeff 2)=A (h : Coeff 2) := by
    dsimp only [L]
    rw [fderiv_hillMixedSupportedPeriodMap_root_eq_restriction q hq hr h0q h0r N n a p hF]
    exact hfixed
  apply Subtype.ext
  change Coeff.positiveDeletedProjection 2 (0 : ℤ)
    (A ((Coeff.positiveDeletedToPositive 2 (n : ℤ) h) : Coeff 2)+
      Coeff.positiveDeletedProjection 2 (n : ℤ) ((Coeff.positiveDeletedToPositive 2 (n : ℤ) h) : Coeff 2)-
      Coeff.positiveDeletedProjection 2 (0 : ℤ) ((Coeff.positiveDeletedToPositive 2 (n : ℤ) h) : Coeff 2))=
    (Coeff.positiveDeletedToPositive 2 (n : ℤ) (L h) : Coeff 2)
  rw [Coeff.positiveDeletedToPositive_coe,Coeff.positiveDeletedToPositive_coe,
    Coeff.positiveDeleted_fixed,Coeff.positiveProjection_fixed_of_positiveDeleted,add_sub_cancel_right,←hL]
  exact Coeff.positiveProjection_fixed_of_positiveDeleted 2 (n : ℤ) (L h)

theorem hillMixedSupportedPeriodMap_root_lower_bound_of_extended
    (N n : ℕ) (hn : 1≤n) (a p : Coeff 2) (C : ℝ)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a)
    (hbound : ∀ h : PositiveDeletedCoeff 2 (0 : ℤ),
      ‖h‖≤C*‖hillExtendedPositivePeriodJacobian q hq hr h0q h0r N n a p h‖) :
    ∀ h : PositiveDeletedCoeff 2 (n : ℤ), ‖h‖≤C*‖fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0 h‖ := by
  intro h
  have hh := hbound (Coeff.positiveDeletedToPositive 2 (n : ℤ) h)
  rw [hillExtendedPositivePeriodJacobian_on_positiveDeleted q hq hr h0q h0r N n hn a p hF h,
    Coeff.norm_positiveDeletedToPositive,Coeff.norm_positiveDeletedToPositive] at hh
  exact hh

end NLS.KdV
