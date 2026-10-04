import NLS.SequenceSpaces.RefinedProductMajorant

/-! # Refined cubic products, including quasi-normed exponents

Three lp sequences multiply into l(p/3). Inclusion into any larger
positive finite exponent is contractive, with no Banach assumption
on the intermediate half or third exponents.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

theorem thirdExponent_eq_div {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    ENNReal.ofReal (p.toReal/3) = p/3 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3),ENNReal.ofReal_toReal hp]
  norm_num

theorem holderTriple_half_third (p : ℝ≥0∞) : (p/2).HolderTriple p (p/3) := by
  rw [ENNReal.holderTriple_iff,
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  simp only [div_eq_mul_inv]
  rw [show (3:ℝ≥0∞) = 2+1 by norm_num,add_mul,one_mul]

/-- The actual triple product retains a sharp norm bound at every
finite positive exponent at least p/3. -/
theorem exists_refined_triple_product {p r : ℝ≥0∞}
    (hp : p ≠ ⊤) (hp0 : 0 < p) (hr : r ≠ ⊤) (hr0 : 0 < r)
    (hpr : ENNReal.ofReal (p.toReal/3) ≤ r) (a b c : Coeff p) :
    ∃ H : Coeff r, (∀ k, H k = a k*b k*c k) ∧ ‖H‖ ≤ ‖a‖*‖b‖*‖c‖ := by
  let : p.HolderTriple p (p/2) := holderTriple_half p
  let : (p/2).HolderTriple p (p/3) := holderTriple_half_third p
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hp
  have hhalf : 0 < (p/2).toReal := by simpa using half_pos ht
  have hthird : 0 < p/3 := by
    rw [← thirdExponent_eq_div hp]
    exact ENNReal.ofReal_pos.mpr (div_pos ht (by norm_num))
  have hpr' : p/3 ≤ r := by rwa [thirdExponent_eq_div hp] at hpr
  let P := quasiHolderProduct (r := p/2) a b
  let Q := quasiHolderProduct (r := p/3) P c
  let H : Coeff r := ⟨fun k => Q k,(lp.memℓp Q).of_exponent_ge hpr'⟩
  refine ⟨H,fun _ => rfl,?_⟩
  apply (norm_quasiExponentInclusion_le hthird hr0 hr hpr' Q).trans
  exact (norm_quasiHolderProduct_le hhalf ht P c).trans
    (mul_le_mul_of_nonneg_right (norm_quasiHolderProduct_le ht ht a b) (lp.norm_nonneg' c))

end NLS.Coeff
