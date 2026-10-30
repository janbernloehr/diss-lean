import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct

/-!
# The exact zeros of the literal auxiliary product

Absolute summability of factor errors gives nonvanishing away from all
retained numerator roots. Conversely, a retained zero factor annihilates
the product. Both directions hold on the natural omitted-gap domain.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absolute convergence makes the literal auxiliary product nonzero away from retained roots. -/
theorem sourcePsiZeta_ne_zero_of_off_retained
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hroots : ∀ k : ℤ, k ≠ n → k ≠ m → z ≠ displacedRoots a k) :
    sourcePsiZeta hp hp1 n m a ψ z ≠ 0 := by
  have hf (k : ℤ) : sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z k ≠ 0 := by
    by_cases hk : k = n ∨ k = m
    · simp [sourcePsiDoubleOmittedFactor,hk]
    · simp only [sourcePsiDoubleOmittedFactor,if_neg hk]
      exact div_ne_zero (sub_ne_zero.mpr (hroots k (not_or.mp hk).1 (not_or.mp hk).2).symm)
        (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ k z (hz k (not_or.mp hk).2))
  have hprod : sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable
      (f := fun k => sourcePsiDoubleOmittedFactor hp hp1 n m a ψ z k-1)
      (by intro k; simpa only [add_comm (1 : ℂ), sub_add_cancel] using hf k)
      (summable_norm_sourcePsiDoubleOmittedFactor_sub_one hp hp1 n m a ψ z)
    simpa only [add_comm (1 : ℂ), sub_add_cancel,sourcePsiDoubleOmittedProduct] using h
  exact mul_ne_zero (div_ne_zero Complex.I_ne_zero
    (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n hmn.symm))) hprod

/-- On its natural spectral domain, the auxiliary product has exactly the retained numerator roots. -/
theorem sourcePsiZeta_eq_zero_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourcePsiZeta hp hp1 n m a ψ z = 0 ↔
      ∃ k : ℤ, k ≠ n ∧ k ≠ m ∧ displacedRoots a k = z := by
  constructor
  · intro hzero
    by_contra h
    apply sourcePsiZeta_ne_zero_of_off_retained hp hp1 n m hmn a ψ z hz _ hzero
    intro k hkn hkm he
    exact h ⟨k,hkn,hkm,he.symm⟩
  · rintro ⟨k,hkn,hkm,hk⟩
    have hprod : sourcePsiDoubleOmittedProduct hp hp1 n m a ψ z = 0 := by
      apply tprod_of_exists_eq_zero
      exact ⟨k,by simp [sourcePsiDoubleOmittedFactor,hkn,hkm,hk]⟩
    simp only [sourcePsiZeta,hprod,mul_zero]

end NLS.ZakharovShabat
