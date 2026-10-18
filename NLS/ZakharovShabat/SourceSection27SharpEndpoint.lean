import NLS.ZakharovShabat.SourceH1SharpEndpoint
import NLS.ZakharovShabat.SourceSection27Original

/-! # Lemma 27.2 with its printed constant at every order

The unrestricted H1 bound completes the original indexed-action estimate
for all m>=1. The same retained Section 27 family satisfies this exact
statement without altering its existing weaker fields.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
/-- Lemma 27.2 at m=1, with the literal original indexed actions and no smallness premise. -/
theorem sourceSection27_endpoint (a : realTypeHigherSobolevSourceLocus 1) :
    (sobolevOddHamiltonian 1 le_rfl a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n)+
      (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n) := by
  rw [sourceSection27_H3_bridge]
  simpa only [sourceIndexedWeightedActionTerm_eq,sourceH1RealSource_realHigherSobolevToH1] using
    sourceH1_energy_le_lemma272 (realHigherSobolevToH1 1 le_rfl a)

/-- Lemma 27.2 with its exact printed coefficient at every order m>=1. -/
theorem sourceSection27_hamiltonian_estimate_literal (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) := by
  by_cases h : 2 ≤ m
  · exact sourceSection27_hamiltonian_estimate m h a
  · have hm1 : m=1 := by omega
    subst m
    simpa only [Nat.mul_one,Nat.sub_self,pow_zero,one_mul,Nat.reduceSub,pow_one] using sourceSection27_endpoint a

/-- The same retained original family also satisfies the unqualified printed estimate. -/
theorem SourceSection27Data.hamiltonian_estimate_literal
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (_Q : SourceSection27Data D A B U T) (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) :=
  sourceSection27_hamiltonian_estimate_literal m hm a

end NLS.ZakharovShabat
