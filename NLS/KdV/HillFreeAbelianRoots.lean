import NLS.KdV.HillAbelianNormalizationProblem
import NLS.KdV.HillAbelianProductZeros

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV



def hillFreeGapRoot (k : ℕ) : ℝ := freeHillValue (k+1 : ℕ)

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillGapRootBox_zero_iff (σ : ℕ → ℝ) :
    σ ∈ hillGapRootBox 0 hq hr ↔ σ = hillFreeGapRoot := by
  have hl (k : ℕ) : hillRealLabels 0 hq hr (2*(k+1)-1) = hillFreeGapRoot k := by
    rw [hillRealLabels_zero]
    congr 1
    omega
  have hu (k : ℕ) : hillRealLabels 0 hq hr (2*(k+1)) = hillFreeGapRoot k := by
    rw [hillRealLabels_zero]
    congr 1
    omega
  constructor
  · intro h
    funext k
    have hs := h k
    rw [hl,hu] at hs
    exact le_antisymm hs.2 hs.1
  · rintro rfl k
    rw [hl,hu]
    exact ⟨le_rfl,le_rfl⟩

theorem hillFreeGapRoot_mem_box : hillFreeGapRoot ∈ hillGapRootBox 0 hq hr :=
  (hillGapRootBox_zero_iff hq hr hillFreeGapRoot).mpr rfl

theorem hillGapRootEnergyFactor_free (k : ℕ) (z : ℂ) :
    hillGapRootEnergyFactor hillFreeGapRoot k z = hillEnergyRootFactor 0 hq hr (k+1) z := by
  rw [hillEnergyRootFactor_zero hq hr (k+1) (by omega)]
  unfold hillGapRootEnergyFactor hillFreeGapRoot
  rw [sub_div,div_self (hillGapRootEnergyFactor_denominator_ne_zero k)]

theorem hillFreeEnergyRootProduct_factorization (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    hillEnergyRootProduct 0 hq hr z = hillEnergyRootFactor 0 hq hr n z *
      hillAbelianNumeratorProduct hillFreeGapRoot n z := by
  have hp := (hasProd_ite_eq (n-1) (hillEnergyRootFactor 0 hq hr n z)).mul
    ((multipliable_hillAbelianNumeratorFactors 0 hq hr hillFreeGapRoot
      (hillFreeGapRoot_mem_box hq hr) n z).hasProd)
  have he (k : ℕ) :
      (if k = n-1 then hillEnergyRootFactor 0 hq hr n z else 1)*
        hillAbelianNumeratorFactor hillFreeGapRoot n k z =
          hillEnergyRootFactor 0 hq hr (k+1) z := by
    unfold hillAbelianNumeratorFactor
    by_cases hk : k = n-1
    · have hkn : k+1 = n := by omega
      rw [if_pos hk,if_pos hkn,hkn,mul_one]
    · have hkn : k+1 ≠ n := by omega
      rw [if_neg hk,if_neg hkn,one_mul,hillGapRootEnergyFactor_free hq hr]
  simp only [he] at hp
  exact hp.tprod_eq

end NLS.KdV
