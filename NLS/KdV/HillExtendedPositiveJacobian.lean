import NLS.KdV.HillExtendedMixedJacobianLimit
import NLS.KdV.HillFullMixedSupportedFredholm
import Mathlib.Analysis.Normed.Operator.Bilinear

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

/-- Restriction of the actual extended mixed Jacobian to the full
positive Hilbert root space, with its omitted coordinate filled by -Id. -/
def hillExtendedPositivePeriodJacobian (N n : ℕ) (a p : Coeff 2) :
    PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (0 : ℤ) :=
  (Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)).comp
    ((hillExtendedMixedPeriodJacobian q hq hr h0q h0r N n a p).comp
      (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL)

theorem fderiv_hillFullMixedSupportedPeriodMap_root_eq_restriction
    (N : ℕ) (a p : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a) :
    fderiv ℂ (fun b : PositiveDeletedCoeff 2 (0 : ℤ) =>
      hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,p)) 0=
      (Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)).comp
        ((fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a).comp
          (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL) := by
  let inc : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL
  let P := Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)
  have hi : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) inc 0 :=
    inc.hasFDerivAt.const_add a
  have hG : HasFDerivAt (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p))
      (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a)
      (a+((0 : PositiveDeletedCoeff 2 (0 : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using hF.hasFDerivAt
  have hd := P.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (0 : ℤ))
    (hG.comp (f := fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) 0 hi)
  convert! hd.fderiv using 1

theorem tendsto_hillExtendedPositivePeriodJacobian_of_ambient
    {ι : Type*} {l : Filter ι} (N : ℕ) (n : ι → ℕ) (a : ι → Coeff 2) (a0 p : Coeff 2)
    (hFull : DifferentiableAt ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a0)
    (hlim : Tendsto (fun i => hillExtendedMixedPeriodJacobian q hq hr h0q h0r N (n i) (a i) p) l
      (𝓝 (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a0))) :
    Tendsto (fun i => hillExtendedPositivePeriodJacobian q hq hr h0q h0r N (n i) (a i) p) l
      (𝓝 (fderiv ℂ (fun b : PositiveDeletedCoeff 2 (0 : ℤ) =>
        hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a0 (b,p)) 0)) := by
  let inc : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL
  let P := Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)
  let R : (Coeff 2 →L[ℂ] Coeff 2) → (PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (0 : ℤ)) :=
    fun T => P.comp (T.comp inc)
  have hR : Continuous R := by
    exact (continuous_id.clm_comp_const inc).const_clm_comp P
  rw [fderiv_hillFullMixedSupportedPeriodMap_root_eq_restriction q hq hr h0q h0r N a0 p hFull]
  exact hR.continuousAt.tendsto.comp hlim

end NLS.KdV
