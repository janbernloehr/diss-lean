import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Original real mean-zero weighted Fourier spaces at every Banach exponent

Physical Fourier reality and zero mean define a closed real subspace of
the literal weighted lp norm. No change of normalization is imposed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- ACTUAL raw weighted sequences with physical Fourier reality and mean
zero, carrying the inherited ORIGINAL weighted lp norm. -/
def physicalRealMeanZeroWeightedExponent (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)] : Submodule ℝ (WeightedCoeff w p) where
  carrier := {q | (∀ j : ℤ, q.val (-j)=conj (q.val j)) ∧ q.val 0=0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro a b ha hb
    constructor
    · intro j
      change a.val (-j)+b.val (-j)=conj (a.val j+b.val j)
      rw [map_add,ha.1 j,hb.1 j]
    · change a.val 0+b.val 0=0
      rw [ha.2,hb.2,add_zero]
  smul_mem' := by
    intro r a ha
    constructor
    · intro j
      change (r : ℂ)*a.val (-j)=conj ((r : ℂ)*a.val j)
      rw [map_mul,conj_ofReal,ha.1 j]
    · change (r : ℂ)*a.val 0=0
      rw [ha.2,mul_zero]

@[simp] theorem mem_physicalRealMeanZeroWeightedExponent (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)] (q : WeightedCoeff w p) :
    q∈physicalRealMeanZeroWeightedExponent w p ↔
      (∀ j : ℤ, q.val (-j)=conj (q.val j)) ∧ q.val 0=0 := Iff.rfl

/-- Physical Fourier reality and zero mean are closed in the original norm. -/
theorem isClosed_physicalRealMeanZeroWeightedExponent
    (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)] :
    IsClosed (physicalRealMeanZeroWeightedExponent w p : Set (WeightedCoeff w p)) := by
  have hreal : IsClosed {q : WeightedCoeff w p | ∀ n : ℤ, q.val (-n)=conj (q.val n)} := by
    have he : {q : WeightedCoeff w p | ∀ n : ℤ, q.val (-n)=conj (q.val n)}=
        ⋂ n : ℤ, {q : WeightedCoeff w p | q.val (-n)=conj (q.val n)} := by
      ext q;simp only [mem_ofPred_eq,mem_iInter]
    rw [he]
    exact isClosed_iInter (fun n => isClosed_eq (WeightedCoeff.evalCLM w p (-n)).continuous
      (continuous_conj.comp (WeightedCoeff.evalCLM w p n).continuous))
  exact hreal.inter (isClosed_eq (WeightedCoeff.evalCLM w p 0).continuous continuous_const)

instance (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)] :
    CompleteSpace (physicalRealMeanZeroWeightedExponent w p) :=
  (isClosed_physicalRealMeanZeroWeightedExponent w p).completeSpace_coe

end NLS
