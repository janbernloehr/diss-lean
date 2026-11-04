import NLS.ZakharovShabat.SourceComponentSwapActions
import NLS.ZakharovShabat.SourceFiniteGapHigherActionTrace

/-! # Physical hierarchy parity under unsigned component exchange

The actual finite-gap locus is invariant under the reflected gap indexing.
The physical trace formula and the higher-action reflection then give the
parity of every independently defined differential Hamiltonian.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Component exchange preserves actual spectral finite-gap sources. -/
theorem realSourceComponentSwap_mem_finiteGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    realSourceComponentSwap φ ∈ sourceFiniteGapLocus hp hp1 := by
  change {n : ℤ | canonicalPeriodicGap hp hp1
    (periodOnePotential (sourceComponentSwap φ.val)) (periodOnePotential_mem _) n ≠ 0}.Finite
  have hset : {n : ℤ | canonicalPeriodicGap hp hp1
      (periodOnePotential (sourceComponentSwap φ.val)) (periodOnePotential_mem _) n ≠ 0} =
      Neg.neg '' {n : ℤ | canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0} := by
    ext n
    simp only [mem_ofPred_eq, sourcePeriodicGap_componentSwap hp hp1 φ.val n, mem_image]
    constructor
    · intro hn
      exact ⟨-n,hn,neg_neg n⟩
    · rintro ⟨k,hk,rfl⟩
      simpa only [neg_neg] using hk
  rw [hset]
  exact hf.image Neg.neg

/-- All positive-order physical Hamiltonians have the original hierarchy
parity, without defining their values by a spectral sum. -/
theorem sourceFiniteGapNLSHamiltonian_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian hp hp1 (realSourceComponentSwap φ)
      (realSourceComponentSwap_mem_finiteGap hp hp1 φ hf) (k+1) =
      (-1 : ℂ)^k * sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1) := by
  have hs := sourceFiniteGap_tsum_higherActions_eq_hamiltonian hp hp1
    (realSourceComponentSwap φ) (realSourceComponentSwap_mem_finiteGap hp hp1 φ hf) k
  have hsum : (∑' n : ℤ, (sourceRealHigherAction hp hp1 (realSourceComponentSwap φ) n k : ℂ)) =
      (-1 : ℂ)^k * ∑' n : ℤ, (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
    simp only [sourceRealHigherAction_componentSwap hp hp1 φ, ofReal_mul, ofReal_pow,
      ofReal_neg, ofReal_one]
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.neg ℤ).tsum_eq (fun n => (sourceRealHigherAction hp hp1 φ n k : ℂ))
  rw [hsum, sourceFiniteGap_tsum_higherActions_eq_hamiltonian hp hp1 φ hf k] at hs
  have hpow : (2 : ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (div_left_inj' hpow).mp
  rw [← hs]
  ring

/-- In particular the physical fourth Hamiltonian changes sign. -/
theorem sourceFiniteGapFourthHamiltonian_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapNLSHamiltonian hp hp1 (realSourceComponentSwap φ)
      (realSourceComponentSwap_mem_finiteGap hp hp1 φ hf) 4 =
      -sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4 := by
  simpa only [show (3 : ℕ)+1 = 4 from rfl, show (-1 : ℂ)^3 = -1 by norm_num,
    neg_one_mul] using sourceFiniteGapNLSHamiltonian_componentSwap hp hp1 φ hf 3

end NLS.ZakharovShabat
