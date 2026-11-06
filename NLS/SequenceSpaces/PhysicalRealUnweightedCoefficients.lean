import NLS.SequenceSpaces.CoefficientCompactness
import NLS.SequenceSpaces.Reflection

/-! # The physical real form of original unweighted coefficients

Conjugate reflection defines a closed real Banach subspace in the
original coefficient norm. Bounded sequences retain this real form in
coefficientwise subsequential limits.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def physicalRealSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Coeff p) where
  carrier := {a | ∀ n, a n = conj (a (-n))}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro a b ha hb n
    change a n+b n = conj (a (-n)+b (-n))
    rw [map_add,ha n,hb n]
  smul_mem' := by
    intro r a ha n
    change (r : ℂ)*a n = conj ((r : ℂ)*a (-n))
    rw [map_mul,Complex.conj_ofReal,ha n]

theorem isClosed_physicalRealSubmodule : IsClosed (physicalRealSubmodule p : Set (Coeff p)) := by
  change IsClosed {a : Coeff p | ∀ n, a n = conj (a (-n))}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  exact isClosed_eq (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous
    (Complex.conjCLE.continuous.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p (-n)).continuous)

instance physicalRealSubmoduleComplete [CompleteSpace (Coeff p)] : CompleteSpace (physicalRealSubmodule p) :=
  isClosed_physicalRealSubmodule.completeSpace_coe

theorem exists_physicalReal_coefficientwise_subseq (a : ℕ → physicalRealSubmodule p)
    (hb : Bornology.IsBounded (range a)) :
    ∃ b : physicalRealSubmodule p, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℤ, Tendsto (fun k => (a (σ k)).val n) atTop (𝓝 (b.val n)) := by
  obtain ⟨M,hM⟩ := hb.exists_norm_le
  have hba : Bornology.IsBounded (range (fun k => (a k).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hM _ ⟨k,rfl⟩
  obtain ⟨b,σ,hσ,ht⟩ := exists_coefficientwise_tendsto_subseq_of_bounded (fun k => (a k).val) hba
  have hr : ∀ n, b n = conj (b (-n)) := by
    intro n
    have hc := Complex.continuous_conj.continuousAt.tendsto.comp (ht (-n))
    exact tendsto_nhds_unique (ht n) (hc.congr (fun k => (a (σ k)).property n |>.symm))
  exact ⟨⟨b,hr⟩,σ,hσ,ht⟩

end NLS.Coeff
