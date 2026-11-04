import NLS.ComplexAnalysis.SignedProductEstimates

/-! # Relative perturbations of convergent complex products

An absolute perturbation estimate compares two actual products. Neither
logarithms nor a complex-valued mean-value point is used. -/
noncomputable section
set_option autoImplicit false
namespace NLS.ComplexAnalysis

/-- Relative factor perturbations give an exact product factorization. -/
theorem product_eq_mul_relative {ι : Type*} (a b u : ι → ℂ) (A B : ℂ)
    (ha : HasProd a A) (hb : HasProd b B) (hu : Summable (fun i => ‖u i‖))
    (he : ∀ i, a i = b i*(1+u i)) :
    A = B*(∏' i, (1+u i)) := by
  have hp := hb.mul (multipliable_one_add_of_summable hu).hasProd
  exact ha.unique (hp.congr_fun he)

/-- The difference is controlled linearly by the absolute relative perturbation sum. -/
theorem norm_product_difference_le {ι : Type*} (a b u : ι → ℂ) (A B : ℂ)
    (ha : HasProd a A) (hb : HasProd b B) (hu : Summable (fun i => ‖u i‖))
    (he : ∀ i, a i = b i*(1+u i)) :
    ‖A-B‖ ≤ ‖B‖*Real.exp (∑' i, ‖u i‖)*(∑' i, ‖u i‖) := by
  rw [product_eq_mul_relative a b u A B ha hb hu he]
  have hbnd := (norm_tprod_one_add_sub_one_le_exp_sub_one_le u hu).1.trans
    (norm_tprod_one_add_sub_one_le_exp_sub_one_le u hu).2
  calc
    _ = ‖B‖*‖(∏' i, (1+u i))-1‖ := by rw [← norm_mul]; congr 1; ring
    _ ≤ ‖B‖*((∑' i, ‖u i‖)*Real.exp (∑' i, ‖u i‖)) :=
      mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
    _ = _ := by ring

/-- Uniform bounds on the base product and perturbation sum give a common Lipschitz constant. -/
theorem norm_product_difference_le_uniform {ι : Type*} (a b u : ι → ℂ) (A B : ℂ)
    (ha : HasProd a A) (hb : HasProd b B) (hu : Summable (fun i => ‖u i‖))
    (he : ∀ i, a i = b i*(1+u i)) (M L : ℝ) (hM : ‖B‖ ≤ M)
    (hL : (∑' i, ‖u i‖) ≤ L) :
    ‖A-B‖ ≤ M*Real.exp L*(∑' i, ‖u i‖) := by
  exact (norm_product_difference_le a b u A B ha hb hu he).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hM (Real.exp_le_exp.mpr hL) (Real.exp_nonneg _) ((norm_nonneg _).trans hM))
      (tsum_nonneg (fun _ => norm_nonneg _)))
end NLS.ComplexAnalysis
