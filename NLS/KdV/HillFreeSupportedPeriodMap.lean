import NLS.KdV.HillFreePeriodDerivative
import NLS.SequenceSpaces.PositiveDeletedSpace
import NLS.ComplexAnalysis.AnalyticLocalInverseCriterion

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeScaledPeriodSequence_supported (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) :
    Coeff.positiveDeletedProjection 2 (n : ℤ) (hillFreeScaledPeriodSequence hq hr n hn a) =
      hillFreeScaledPeriodSequence hq hr n hn a := by
  apply (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) _).mpr
  intro m hm
  rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_neg (by omega)]

def hillFreeSupportedPeriodMap (n : ℕ) (hn : 1 ≤ n) :
    PositiveDeletedCoeff 2 (n : ℤ) → PositiveDeletedCoeff 2 (n : ℤ) :=
  fun a => Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
    (hillFreeScaledPeriodSequence hq hr n hn a)

theorem hillFreeSupportedPeriodMap_coe (n : ℕ) (hn : 1 ≤ n)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) :
    (hillFreeSupportedPeriodMap hq hr n hn a : Coeff 2) =
      hillFreeScaledPeriodSequence hq hr n hn (a : Coeff 2) := by
  exact hillFreeScaledPeriodSequence_supported hq hr n hn a

theorem analyticOnNhd_hillFreeSupportedPeriodMap (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillFreeSupportedPeriodMap hq hr n hn) univ := by
  intro a _
  have hinc := (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL.analyticAt a
  exact ((Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).analyticAt _).comp
    ((analyticOnNhd_hillFreeScaledPeriodSequence hq hr n hn _ (mem_univ _)).comp hinc)

theorem hasFDerivAt_hillFreeSupportedPeriodMap_zero (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (hillFreeSupportedPeriodMap hq hr n hn)
      (-ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))) 0 := by
  let L : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let P := Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
  have hf : HasFDerivAt (hillFreeScaledPeriodSequence hq hr n hn)
      (-Coeff.positiveDeletedProjection 2 (n : ℤ)) (0 : Coeff 2) := by
    rw [← fderiv_hillFreeScaledPeriodSequence_zero hq hr n hn]
    exact (analyticOnNhd_hillFreeScaledPeriodSequence hq hr n hn 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := P.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (n : ℤ))
    (hf.comp (0 : PositiveDeletedCoeff 2 (n : ℤ)) L.hasFDerivAt)
  have hL : P.comp ((-Coeff.positiveDeletedProjection 2 (n : ℤ)).comp L) =
      -ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)) := by
    apply ContinuousLinearMap.ext
    intro a
    apply Subtype.ext
    change Coeff.positiveDeletedProjection 2 (n : ℤ)
      (-Coeff.positiveDeletedProjection 2 (n : ℤ) (a : Coeff 2)) = -(a : Coeff 2)
    rw [map_neg,Coeff.positiveDeletedProjection_idempotent,Coeff.positiveDeleted_fixed]
  rw [hL] at hc
  convert! hc using 1

theorem hillFreeSupportedPeriodMap_zero (n : ℕ) (hn : 1 ≤ n) :
    hillFreeSupportedPeriodMap hq hr n hn 0 = 0 := by
  apply Subtype.ext
  rw [hillFreeSupportedPeriodMap_coe]
  exact hillFreeScaledPeriodSequence_zero hq hr n hn

theorem exists_hillFreeSupportedPeriodMap_localInverse (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : PositiveDeletedCoeff 2 (n : ℤ) → PositiveDeletedCoeff 2 (n : ℤ),
      AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
        (∀ᶠ a in 𝓝 (0 : PositiveDeletedCoeff 2 (n : ℤ)),
          G (hillFreeSupportedPeriodMap hq hr n hn a) = a) ∧
        (∀ᶠ b in 𝓝 (0 : PositiveDeletedCoeff 2 (n : ℤ)),
          hillFreeSupportedPeriodMap hq hr n hn (G b) = b) := by
  have hF := analyticOnNhd_hillFreeSupportedPeriodMap hq hr n hn 0 (mem_univ _)
  have hu : IsUnit (fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) 0) := by
    rw [(hasFDerivAt_hillFreeSupportedPeriodMap_zero hq hr n hn).fderiv]
    exact (show IsUnit (1 : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ)) from
      isUnit_one).neg
  have hi := (isUnit_fderiv_iff_localInverse hF).mp hu
  rw [hillFreeSupportedPeriodMap_zero hq hr n hn] at hi
  exact hi

end NLS.KdV
