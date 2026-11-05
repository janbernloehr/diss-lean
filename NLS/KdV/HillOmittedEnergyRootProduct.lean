import NLS.KdV.HillEnergyChiPositivity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillOmittedEnergyRootFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n k : ℕ) (z : ℂ) : ℂ :=
  if k+1 = n then 1 else hillEnergyRootFactor q hq hr (k+1) z

theorem analyticOnNhd_hillOmittedEnergyRootFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n k : ℕ) :
    AnalyticOnNhd ℂ (hillOmittedEnergyRootFactor q hq hr n k) (hillGapFilledDomain q hq hr n) := by
  intro z hz
  unfold hillOmittedEnergyRootFactor
  by_cases hk : k+1 = n
  · simp only [if_pos hk]
    exact analyticAt_const
  · simp only [if_neg hk]
    exact (analyticOnNhd_endpointRoot _ _ z
      (not_mem_other_gap_of_mem_hillGapFilledDomain q hq hr n (k+1) (by omega) hk z hz)).div_const


theorem exists_hillOmittedEnergyRootFactor_bounded_majorant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖hillOmittedEnergyRootFactor q hq hr n k z-1‖ ≤ u k := by
  obtain ⟨N,u,hu,hbound⟩ := exists_hillEnergyRootFactor_bounded_majorant q hq hr R hR
  refine ⟨N,u,hu,?_⟩
  intro k hk z hz
  unfold hillOmittedEnergyRootFactor
  split_ifs
  · simp only [sub_self,norm_zero]
    exact (norm_nonneg _).trans (hbound k hk z hz)
  · exact hbound k hk z hz

def hillOmittedEnergyRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  ∏' k : ℕ, hillOmittedEnergyRootFactor q hq hr n k z

theorem hasProdUniformlyOn_hillOmittedEnergyRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ)
    (K : Set ℂ) (hK : IsCompact K) (hdom : K ⊆ hillGapFilledDomain q hq hr n) :
    HasProdUniformlyOn (fun k z => hillOmittedEnergyRootFactor q hq hr n k z)
      (hillOmittedEnergyRootProduct q hq hr n) K := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N,u,hu,hmajor⟩ := exists_hillOmittedEnergyRootFactor_bounded_majorant q hq hr n R hR.le
  have hevent : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K, ‖hillOmittedEnergyRootFactor q hq hr n k z-1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact fun z hz => hmajor k hk z (hbound z hz)
  have hc (k : ℕ) : ContinuousOn (fun z => hillOmittedEnergyRootFactor q hq hr n k z-1) K :=
    (((analyticOnNhd_hillOmittedEnergyRootFactor q hq hr n k).continuousOn).mono hdom).sub continuousOn_const
  have hp := hu.hasProdUniformlyOn_one_add hK hevent hc
  have he (k : ℕ) (z : ℂ) : 1+(hillOmittedEnergyRootFactor q hq hr n k z-1) = hillOmittedEnergyRootFactor q hq hr n k z := by ring
  simp only [he] at hp
  convert! hp using 1

theorem hasProdLocallyUniformlyOn_hillOmittedEnergyRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    HasProdLocallyUniformlyOn (fun k z => hillOmittedEnergyRootFactor q hq hr n k z)
      (hillOmittedEnergyRootProduct q hq hr n) (hillGapFilledDomain q hq hr n) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact (isOpen_hillGapFilledDomain q hq hr n)
  exact fun K hKsub hK => hasProdUniformlyOn_hillOmittedEnergyRootFactors q hq hr n K hK hKsub

theorem analyticOnNhd_hillOmittedEnergyRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    AnalyticOnNhd ℂ (hillOmittedEnergyRootProduct q hq hr n) (hillGapFilledDomain q hq hr n) := by
  have hf (k : ℕ) : DifferentiableOn ℂ (hillOmittedEnergyRootFactor q hq hr n k) (hillGapFilledDomain q hq hr n) :=
    (analyticOnNhd_hillOmittedEnergyRootFactor q hq hr n k).differentiableOn
  have hd : DifferentiableOn ℂ (hillOmittedEnergyRootProduct q hq hr n) (hillGapFilledDomain q hq hr n) :=
    (hasProdLocallyUniformlyOn_hillOmittedEnergyRootFactors q hq hr n).differentiableOn
      (Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd (fun k _ => hf k))) (isOpen_hillGapFilledDomain q hq hr n)
  exact hd.analyticOnNhd (isOpen_hillGapFilledDomain q hq hr n)

end NLS.KdV
