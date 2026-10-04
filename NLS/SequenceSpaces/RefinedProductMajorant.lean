import NLS.SequenceSpaces.QuasiHolderProduct
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-! # Refined exponents for products of coefficient sequences

The quasi-normed Hölder product lies at half the original exponent.
Contractive exponent inclusion preserves its norm bound at every larger
positive finite exponent, without a Banach assumption at the half exponent.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- A product of two lp sequences has a majorant at every finite positive
exponent at least p/2, with Hölder constant one even when p/2 is below one. -/
theorem exists_refined_product_majorant {p r : ℝ≥0∞}
    (hp : p ≠ ⊤) (hp0 : 0 < p) (hr : r ≠ ⊤) (hr0 : 0 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) (a b : Coeff p) :
    ∃ H : Coeff r, (∀ k, ‖a k‖*‖b k‖ ≤ ‖H k‖) ∧ ‖H‖ ≤ ‖a‖*‖b‖ := by
  let : p.HolderTriple p (p/2) := holderTriple_half p
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hp
  have hhalf : 0 < p/2 := by
    rw [← halfExponent_eq_div hp]
    exact ENNReal.ofReal_pos.mpr (div_pos ht (by norm_num))
  have hpr' : p/2 ≤ r := by rwa [halfExponent_eq_div hp] at hpr
  let P := quasiHolderProduct (r := p/2) a b
  let H : Coeff r := ⟨fun k => P k,(lp.memℓp P).of_exponent_ge hpr'⟩
  refine ⟨H,fun k => ?_,?_⟩
  · change ‖a k‖*‖b k‖ ≤ ‖a k*b k‖
    rw [norm_mul]
  · exact (norm_quasiExponentInclusion_le hhalf hr0 hr hpr' P).trans
      (norm_quasiHolderProduct_le ht ht a b)

end NLS.Coeff
