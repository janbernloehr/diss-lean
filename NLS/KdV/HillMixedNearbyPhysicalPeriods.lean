import NLS.KdV.HillLocalPhysicalPeriodMatching
import NLS.KdV.HillMixedPhysicalPeriodCoordinates

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

theorem hillMixedComplexPeriodSequence_nearby_physical_coordinate
    (N n k : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≠ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (p : RealPeriodOneHillPotential) (hp : ‖SpectralWeight.one.toCoeff p.val‖ ≤ B)
    (hlo : ∀ k : ℕ, 1 ≤ k → k < N → ∀ n : ℕ, ∀ a : Coeff 2,
      hillAbelianComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff p.val) =
        hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a) (a : Coeff 2) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff p.val) (k : ℤ) =
      (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a := by
  rw [hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n k hn hk,if_pos hkn]
  by_cases hkN : k < N
  · rw [if_pos hkN,hlo k hk hkN n a]
  · rw [if_neg hkN,hillHighAbelianComplexPeriod_eq_intrinsic_physical h0q h0r N hN B D hc p.val p.property.1 p.property.2 hp n k (by omega) a]
    rfl

theorem exists_hillMixedComplexPeriodSequence_physical_zero_neighborhood
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V, ‖SpectralWeight.one.toCoeff p.val‖ ≤ B → ∀ n : ℕ, 1 ≤ n → ∀ a : Coeff 2,
        hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff p.val) = 0 →
        ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a = 0 := by
  obtain ⟨V,hV,hqV,hlo⟩ := exists_hillAbelianComplexPeriods_finite_physical_neighborhood q hq hr N
  refine ⟨V,hV,hqV,?_⟩
  intro p hp hpnorm n hn a hzero k hk hkn
  have he := congrArg (fun c : Coeff 2 => c (k : ℤ)) hzero
  rw [hillMixedComplexPeriodSequence_nearby_physical_coordinate q hq hr h0q h0r N n k hN hn hk hkn B D hc p hpnorm
    (hlo p hp) a] at he
  change (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a = 0 at he
  have hcne : ((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (strictMono_freeHillValue.injective.ne hkn)))
      (by exact_mod_cast (show n ≠ 0 by omega))
  exact (mul_eq_zero.mp he).resolve_left hcne

end NLS.KdV
