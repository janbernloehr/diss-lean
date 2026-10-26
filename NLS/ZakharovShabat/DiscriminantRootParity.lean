import NLS.ZakharovShabat.CanonicalPeriodicLevels
import NLS.ZakharovShabat.FiniteDiscriminant
import NLS.ZakharovShabat.ParityRootMultiplicity

/-! # Exact root-space parity from the actual discriminant level -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero algebraic multiplicity removes the entire parity part of the root space. -/
theorem parityRootSpace_eq_bot_of_multiplicity_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (r : ℤ) (z : ℂ) (h : parityAlgebraicMultiplicity hp φ r z = 0) :
    periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r = ⊥ := by
  let := finiteDimensional_parityRootSpace hp φ r z
  exact Submodule.finrank_eq_zero.mp h

/-- The actual discriminant level fixes the parity of every generalized
periodic eigenvector, with no large-index or cutoff restriction. -/
theorem periodicRootSpaceTop_le_parity_of_discriminant_level
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) (n : ℤ)
    (hz : canonicalDiscriminant hp φ z = if n % 2 = 0 then 2 else -2) :
    periodicRootSpaceTop hp φ z ≤ pairParitySubspace n := by
  have hl := canonicalDiscriminant_parity_levels_finite hp hp1 φ hφ z
  have hs := periodicRootSpaceTop_parity_split hp φ hφ z
  by_cases hn : n % 2 = 0
  · have hm : parityAlgebraicMultiplicity hp φ 1 z = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have he := hl.2.mpr hpos
      rw [if_pos hn] at hz
      norm_num [hz] at he
    have hb := parityRootSpace_eq_bot_of_multiplicity_zero hp φ 1 z hm
    have hr : periodicRootSpaceTop hp φ z ≤ pairParitySubspace 0 := by
      rw [← hs,hb,sup_bot_eq]
      exact inf_le_right
    intro x hx
    simpa only [mem_pairParitySubspace,Coeff.mem_paritySubspace,hn,Int.zero_emod] using hr hx
  · have hm : parityAlgebraicMultiplicity hp φ 0 z = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have he := hl.1.mpr hpos
      rw [if_neg hn] at hz
      norm_num [hz] at he
    have hb := parityRootSpace_eq_bot_of_multiplicity_zero hp φ 0 z hm
    have hr : periodicRootSpaceTop hp φ z ≤ pairParitySubspace 1 := by
      rw [← hs,hb,bot_sup_eq]
      exact inf_le_right
    have hn1 : n % 2 = 1 := by omega
    intro x hx
    simpa [mem_pairParitySubspace,Coeff.mem_paritySubspace,hn1] using hr hx

/-- Both actual ordered endpoints have their signed index parity, including
central indices and collapsed gaps. -/
theorem canonicalPeriodicEndpoints_rootSpace_parity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    periodicRootSpaceTop hp φ (canonicalPeriodicLeft hp hp1 φ hφ n) ≤ pairParitySubspace n ∧
    periodicRootSpaceTop hp φ (canonicalPeriodicRight hp hp1 φ hφ n) ≤ pairParitySubspace n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ hφ hreal n
  exact ⟨periodicRootSpaceTop_le_parity_of_discriminant_level hp hp1 φ hφ _ n hl,
    periodicRootSpaceTop_le_parity_of_discriminant_level hp hp1 φ hφ _ n hr⟩

end NLS.ZakharovShabat
