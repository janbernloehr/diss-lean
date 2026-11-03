import NLS.KdV.HillComplexPeriodAnalytic
import NLS.KdV.HillFreeSupportedPeriodMap

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillComplexScaledPeriodSequence_zero_potential (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) :
    hillComplexScaledPeriodSequence hq hr n (a,0) = hillFreeScaledPeriodSequence hq hr n hn a := by
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  ext m
  rw [hillComplexScaledPeriodSequence_apply_on hq hr n hn ε D hD.le hc (a,0)
    ⟨mem_univ _,mem_ball_self hε⟩ m,hillFreeScaledPeriodSequence_apply,
    hillComplexScaledPeriodCoordinate,hillFreeScaledPeriodCoordinate]
  split_ifs with hm
  · have he := hillAbelianComplexPeriod_at_base 0 hq hr n m.toNat (by omega) a
    rw [map_zero] at he
    rw [he]
  · rfl

theorem hillComplexScaledPeriodSequence_supported (n : ℕ) (t : Coeff 2 × Coeff 2) :
    Coeff.positiveDeletedProjection 2 (n : ℤ) (hillComplexScaledPeriodSequence hq hr n t) =
      hillComplexScaledPeriodSequence hq hr n t := by
  classical
  by_cases h : Memℓp (hillComplexScaledPeriodCoordinate hq hr n t) 2
  · apply (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) _).mpr
    intro m hm
    rw [hillComplexScaledPeriodSequence_apply_of_mem hq hr n t h m,
      hillComplexScaledPeriodCoordinate,if_neg (by omega)]
  · rw [hillComplexScaledPeriodSequence,dif_neg h,map_zero]

def hillComplexSupportedPeriodMap (n : ℕ) :
    (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) → PositiveDeletedCoeff 2 (n : ℤ) :=
  fun t => Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
    (hillComplexScaledPeriodSequence hq hr n ((t.1 : Coeff 2),t.2))

theorem hillComplexSupportedPeriodMap_coe (n : ℕ) (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) :
    (hillComplexSupportedPeriodMap hq hr n t : Coeff 2) =
      hillComplexScaledPeriodSequence hq hr n ((t.1 : Coeff 2),t.2) :=
  hillComplexScaledPeriodSequence_supported hq hr n ((t.1 : Coeff 2),t.2)

theorem hillComplexSupportedPeriodMap_zero_potential (n : ℕ) (hn : 1 ≤ n)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) :
    hillComplexSupportedPeriodMap hq hr n (a,0) = hillFreeSupportedPeriodMap hq hr n hn a := by
  apply Subtype.ext
  rw [hillComplexSupportedPeriodMap_coe,hillFreeSupportedPeriodMap_coe,
    hillComplexScaledPeriodSequence_zero_potential hq hr n hn]

theorem analyticOnNhd_hillComplexSupportedPeriodMap (n : ℕ) (hn : 1 ≤ n) (ε D : ℝ)
    (hD : 0 ≤ D) (hc : HillComplexPeriodControl hq hr ε D) :
    AnalyticOnNhd ℂ (hillComplexSupportedPeriodMap hq hr n) (univ ×ˢ ball 0 ε) := by
  intro t ht
  let L : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  have hJ : AnalyticAt ℂ (fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 =>
      ((v.1 : Coeff 2),v.2)) t := (L.analyticAt t.1 |>.comp analyticAt_fst).prod analyticAt_snd
  exact ((Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).analyticAt _).comp
    ((analyticOnNhd_hillComplexScaledPeriodSequence hq hr n hn ε D hD hc
      ((t.1 : Coeff 2),t.2) ht).comp
        (f := fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => ((v.1 : Coeff 2),v.2)) hJ)

theorem hillComplexSupportedPeriodMap_zero (n : ℕ) (hn : 1 ≤ n) :
    hillComplexSupportedPeriodMap hq hr n (0,0) = 0 := by
  rw [hillComplexSupportedPeriodMap_zero_potential hq hr n hn,hillFreeSupportedPeriodMap_zero hq hr n hn]

end NLS.KdV
