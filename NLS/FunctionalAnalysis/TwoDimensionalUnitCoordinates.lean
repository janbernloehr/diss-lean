import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact unit-energy coordinates in a two-dimensional orthonormal basis. -/
noncomputable section
namespace NLS.FunctionalAnalysis

/-- Coordinates have Euclidean energy one, rather than the maximum norm
of a plain product; in particular each complex coefficient is bounded by one. -/
theorem exists_unit_coordinates_fin_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis (Fin 2) ℂ E) (x : E) (hx : ‖x‖ = 1) :
    ∃ a c : ℂ, x = a • b 0+c • b 1 ∧ ‖a‖^2+‖c‖^2 = 1 ∧ ‖a‖ ≤ 1 ∧ ‖c‖ ≤ 1 := by
  have he : ‖b.repr x 0‖^2+‖b.repr x 1‖^2 = 1 := by
    simpa only [OrthonormalBasis.repr_apply_apply,Fin.sum_univ_two,hx,one_pow] using
      b.sum_sq_norm_inner_right x
  refine ⟨b.repr x 0,b.repr x 1,?_,he,?_,?_⟩
  · simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  · nlinarith [norm_nonneg (b.repr x 0),sq_nonneg ‖b.repr x 1‖]
  · nlinarith [norm_nonneg (b.repr x 1),sq_nonneg ‖b.repr x 0‖]

end NLS.FunctionalAnalysis
