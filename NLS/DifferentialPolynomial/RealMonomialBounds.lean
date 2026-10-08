import NLS.DifferentialPolynomial.JetOrderBounds

/-! # Real monomial bounds for the reduced Hamiltonians

Conjugate jets have equal absolute values. Combining the two field counts at
each order gives the weighted-degree and even-degree restrictions in (5.9),
and the finite positive majorant in (5.10).
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

/-- Combined multiplicity of the two fields at a derivative order. -/
def jetMultiplicity (d : Monomial) (k : ℕ) : ℕ := d (false,k)+d (true,k)

/-- Extend a supported monomial sum to the finite rectangle of lower jets. -/
theorem monomial_sum_lower_jets (s : ℕ) (d : Monomial)
    (hd : ∀ v ∈ d.support, v.2 < s) (f : Jet → ℤ) :
    (∑ v ∈ d.support, (d v:ℤ)*f v) =
      ∑ k ∈ Finset.range s, ((d (false,k):ℤ)*f (false,k)+(d (true,k):ℤ)*f (true,k)) := by
  classical
  have hsub : d.support ⊆ Finset.univ ×ˢ Finset.range s := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr (hd v hv)⟩
  rw [Finset.sum_subset hsub (by intro v _ hv; simp [Finsupp.notMem_support_iff.mp hv]),
    Finset.sum_product,Fintype.sum_bool,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Grouping conjugate factors preserves the homogeneous derivative weight. -/
theorem jetMultiplicity_weight (s : ℕ) (d : Monomial)
    (hd : ∀ v ∈ d.support, v.2 < s) :
    (∑ k ∈ Finset.range s, ((k+1)*jetMultiplicity d k : ℕ) : ℕ) =
      Finsupp.weight totalWeight d := by
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum,nsmul_eq_mul]
  rw [monomial_sum_lower_jets s d hd]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simp only [jetMultiplicity,totalWeight,Nat.cast_add]
  ring

/-- Charge zero forces an even number of fields, as required by (5.9). -/
theorem jetMultiplicity_even (s : ℕ) (d : Monomial)
    (hd : ∀ v ∈ d.support, v.2 < s) (hc : Finsupp.weight fieldCharge d = 0) :
    Even (∑ k ∈ Finset.range s, jetMultiplicity d k) := by
  rw [Finsupp.weight_apply] at hc
  simp only [Finsupp.sum,nsmul_eq_mul] at hc
  rw [monomial_sum_lower_jets s d hd] at hc
  simp only [fieldCharge,Bool.false_eq_true,↓reduceIte,mul_neg,mul_one] at hc
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib] at hc
  have he : (∑ k ∈ Finset.range s, d (false,k)) = ∑ k ∈ Finset.range s, d (true,k) := by
    have h : (∑ k ∈ Finset.range s, (d (false,k):ℤ)) =
        ∑ k ∈ Finset.range s, (d (true,k):ℤ) := by omega
    exact_mod_cast h
  refine ⟨∑ k ∈ Finset.range s, d (true,k),?_⟩
  simp only [jetMultiplicity,Finset.sum_add_distrib,he]

/-- Combining conjugate factors gives a product in the first field alone. -/
theorem monomial_prod_norm_lower_jets (s : ℕ) (d : Monomial)
    (hd : ∀ v ∈ d.support, v.2 < s) (z : Jet → ℂ)
    (hz : ∀ k, ‖z (true,k)‖ = ‖z (false,k)‖) :
    (∏ v ∈ d.support, ‖z v‖^d v) =
      ∏ k ∈ Finset.range s, ‖z (false,k)‖^jetMultiplicity d k := by
  classical
  have hsub : d.support ⊆ Finset.univ ×ˢ Finset.range s := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr (hd v hv)⟩
  rw [Finset.prod_subset hsub (by intro v _ hv; simp [Finsupp.notMem_support_iff.mp hv]),
    Finset.prod_product,Fintype.prod_bool,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [hz,jetMultiplicity,pow_add,mul_comm]

/-- The pointwise majorant (5.10), indexed by the actual finite polynomial support. -/
theorem norm_eval_le_real_monomials (s : ℕ) (hs : 1 ≤ s) (q : Polynomial)
    (hq : JetOrderLE q (s-1)) (z : Jet → ℂ)
    (hz : ∀ k, ‖z (true,k)‖ = ‖z (false,k)‖) :
    ‖MvPolynomial.eval z q‖ ≤ ∑ d ∈ q.support, ‖q.coeff d‖ *
      ∏ k ∈ Finset.range s, ‖z (false,k)‖^jetMultiplicity d k := by
  classical
  rw [MvPolynomial.eval_eq]
  calc
    _ ≤ ∑ d ∈ q.support, ‖q.coeff d * ∏ v ∈ d.support, z v^d v‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [norm_mul,norm_prod]
      simp only [norm_pow]
      rw [monomial_prod_norm_lower_jets s d (fun v hv => by have := hq d hd v hv; omega) z hz]

end NLS.DifferentialPolynomial
