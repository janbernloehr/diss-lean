import NLS.KdV.HillMixedPhysicalPeriodCoordinates
import NLS.SequenceSpaces.PositiveDeletedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillMixedSupportedPeriodMap (N n : ℕ) (a : Coeff 2)
    (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) : PositiveDeletedCoeff 2 (n : ℤ) :=
  Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
    (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a+(t.1 : Coeff 2),t.2))

theorem analyticOnNhd_hillMixedSupportedPeriodMap
    (N n : ℕ) (a : Coeff 2) (U : Set (Coeff 2))
    (hF : AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N n) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n a) (univ ×ˢ U) := by
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  intro t ht
  have hJ : AnalyticAt ℂ (fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => (a+(v.1 : Coeff 2),v.2)) t :=
    (analyticAt_const.add ((inc.analyticAt t.1).comp (f := fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => v.1)
      analyticAt_fst)).prod analyticAt_snd
  have hG := (hF (a+(t.1 : Coeff 2),t.2) ⟨mem_univ _,ht.2⟩).comp
    (f := fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => (a+(v.1 : Coeff 2),v.2)) hJ
  exact ((Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).analyticAt _).comp hG

theorem hillMixedSupportedPeriodMap_base_coordinate
    (N n k : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≠ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (a : Coeff 2) (b : PositiveDeletedCoeff 2 (n : ℤ)) :
    (hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,SpectralWeight.one.toCoeff q) : Coeff 2) (k : ℤ) =
      (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*hillAbelianHilbertPeriod q hq hr n k (a+(b : Coeff 2)) := by
  rw [hillMixedSupportedPeriodMap,Coeff.positiveDeletedProjectionTo_coe,Coeff.positiveDeletedProjection_apply,
    if_pos (show (0 : ℤ) < k ∧ (k : ℤ) ≠ n by constructor <;> omega),
    hillMixedComplexPeriodSequence_at_base_coordinate q hq hr h0q h0r N n k hN hn hk hkn B D hc hp]

theorem hillMixedSupportedPeriodMap_at_global_roots_eq_zero
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0) :
    hillMixedSupportedPeriodMap q hq hr h0q h0r N n
      (hillGapRootHilbertCoordinates q hq hr roots hroots) (0,SpectralWeight.one.toCoeff q) = 0 := by
  rw [hillMixedSupportedPeriodMap]
  simp only [ZeroMemClass.coe_zero,add_zero]
  rw [hillMixedComplexPeriodSequence_at_global_roots_eq_zero q hq hr h0q h0r N n hN hn B D hc hp roots hroots hperiods,map_zero]

end NLS.KdV
