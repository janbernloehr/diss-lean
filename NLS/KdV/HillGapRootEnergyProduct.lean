import NLS.KdV.HillGapSignedRootFrequencies

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillGapSignedRootFrequency_pairedFactor
    (roots : ℕ → ℝ) (z : ℂ) (k : ℕ) :
    singleSpectralFactor (hillGapSignedRootFrequency roots) z ((k+1 : ℕ) : ℤ)*
      singleSpectralFactor (hillGapSignedRootFrequency roots) z (-((k+1 : ℕ) : ℤ)) =
      hillGapRootEnergyFactor roots k (z^2) := by
  have hs : (Complex.sqrt (roots k))^2 = (roots k : ℂ) := by
    have h := Complex.cpow_nat_inv_pow (roots k : ℂ) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hd : (freeHillValue (k+1 : ℕ) : ℂ) = ((Real.pi : ℂ)*(k+1 : ℕ))^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast]
    push_cast
    ring
  simp only [singleSpectralFactor,singleSpectralDenominator,
    if_neg (by omega : ((k+1 : ℕ) : ℤ) ≠ 0),if_neg (by omega : -((k+1 : ℕ) : ℤ) ≠ 0),
    hillGapSignedRootFrequency_natSucc,hillGapSignedRootFrequency_negNatSucc,hillGapRootEnergyFactor]
  rw [hd]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : (k : ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero k
  field_simp
  linear_combination hs

theorem singleSpectralPartialProduct_hillGapSignedRootFrequency
    (roots : ℕ → ℝ) (z : ℂ) (N : ℕ) :
    singleSpectralPartialProduct (hillGapSignedRootFrequency roots) z N =
      -2*z*∏ k ∈ Finset.range N, hillGapRootEnergyFactor roots k (z^2) := by
  rw [singleSpectralPartialProduct,prod_symmetric_interval]
  have hp (k : ℕ) := hillGapSignedRootFrequency_pairedFactor roots z k
  simp only [Nat.cast_add,Nat.cast_one] at hp
  have hzero : singleSpectralFactor (hillGapSignedRootFrequency roots) z 0 = -z := by
    simp only [singleSpectralFactor,singleSpectralDenominator,hillGapSignedRootFrequency,if_true,zero_sub,div_one]
  simp only [hp,hzero]
  ring


theorem entireSingleSpectralProduct_hillGapFullEnergyProduct
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (z : ℂ) :
    entireSingleSpectralProduct (hillGapSignedRootFrequency roots) z =
      -2*z*hillAbelianNumeratorProduct roots 0 (z^2) := by
  have hf := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    (hillGapSignedRootFrequency roots)
    (memℓp_hillGapSignedRootFrequency_displacement q hq hr roots hroots)).tendsto_at (mem_univ z)
  have he := ((multipliable_hillAbelianNumeratorFactors q hq hr roots hroots 0 (z^2)).hasProd.tendsto_prod_nat).const_mul (-2*z)
  simp only [singleSpectralPartialProduct_hillGapSignedRootFrequency] at hf
  have heq (k : ℕ) : hillAbelianNumeratorFactor roots 0 k (z^2) = hillGapRootEnergyFactor roots k (z^2) := by
    simp only [hillAbelianNumeratorFactor,if_neg (by omega : k+1 ≠ 0)]
  simp only [heq] at he
  exact tendsto_nhds_unique hf he

end NLS.KdV
