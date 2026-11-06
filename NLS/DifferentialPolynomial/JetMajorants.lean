import NLS.DifferentialPolynomial.RealMonomialBounds

/-! # Finite lower-jet monomial majorants under pointwise domination. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial

namespace NLS.DifferentialPolynomial

/-- Domination of each lower jet gives a finite scalar monomial majorant. -/
theorem norm_eval_le_lower_jet_majorant (s : ℕ) (hs : 1 ≤ s) (p : Polynomial)
    (hp : JetOrderLE p (s-1)) (z : Jet → ℂ) (U : ℕ → ℝ)
    (hz : ∀ v, v.2 < s → ‖z v‖ ≤ U v.2) :
    ‖MvPolynomial.eval z p‖ ≤ ∑ d ∈ p.support, ‖p.coeff d‖ *
      ∏ k ∈ Finset.range s, (U k)^jetMultiplicity d k := by
  classical
  rw [MvPolynomial.eval_eq]
  calc
    _ ≤ ∑ d ∈ p.support, ‖p.coeff d‖ * ∏ v ∈ d.support, ‖z v‖^d v := by
      simpa only [norm_mul, norm_prod, norm_pow] using
        norm_sum_le (s := p.support) (f := fun d => p.coeff d*∏ v ∈ d.support, z v^d v)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have ho (v : Jet) (hv : v ∈ d.support) : v.2 < s := by
        have := hp d hd v hv
        omega
      calc
        _ ≤ ∏ v ∈ d.support, (U v.2)^d v := by
          apply Finset.prod_le_prod (fun v _ => pow_nonneg (norm_nonneg _) _)
          intro v hv
          exact pow_le_pow_left₀ (norm_nonneg _) (hz v (ho v hv)) _
        _ = _ := by
          have hsub : d.support ⊆ Finset.univ ×ˢ Finset.range s := by
            intro v hv
            exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr (ho v hv)⟩
          rw [Finset.prod_subset hsub (by intro v _ hv; simp [Finsupp.notMem_support_iff.mp hv]),
            Finset.prod_product, Fintype.prod_bool, ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro k _
          simp only [jetMultiplicity, pow_add]
          ring

end NLS.DifferentialPolynomial
