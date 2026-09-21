import NLS.Fourier.UniformAbsoluteSampledRows
import NLS.Fourier.SampledProductEstimates
import NLS.ComplexAnalysis.SmallAbsoluteProducts

/-! # Uniformly small off-diagonal relative-product errors
Small tails and a norm bound give errors arbitrarily close to zero at all
large signed indices, uniformly over the whole half-unit sampling disc.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The absolute row majorant controls the full product error by an exponential. -/
theorem norm_sampledProductError_le_exp_row (hp1 : 1 < p) (hp : p ≠ ⊤)
    (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    ‖sampledProductError hp1 hp t ht a n‖ ≤ Real.exp ‖absoluteSampledRowMajorant hp a n‖-1 := by
  rw [sampledProductError_apply]
  exact (NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_exp _
    (summable_norm_perturbedHilbertSeries hp1 hp t ht a n)).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr (tsum_norm_perturbedHilbert_le_majorant hp t ht a n)) 1)

/-- One input-tail tolerance works with every finite block and every sampling family. -/
theorem exists_uniform_small_sampledProductErrors (hp1 : 1 < p) (hp : p ≠ ⊤)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Finset ℤ, ∃ N : ℕ, ∀ a : Coeff p,
      ‖a‖ ≤ R → ‖a-Coeff.truncate s a‖ ≤ δ →
      ∀ (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2), ∀ n : ℤ, N ≤ n.natAbs →
        ‖sampledProductError hp1 hp t ht a n‖ < ε := by
  obtain ⟨δ,hδ,h⟩ := exists_uniform_small_absoluteSampledRows hp hR
    (Real.log_pos (by linarith : 1 < 1+ε))
  refine ⟨δ,hδ,fun s => ?_⟩
  obtain ⟨N,hN⟩ := h s
  refine ⟨N,fun a ha ht t hsample n hn => ?_⟩
  apply (norm_sampledProductError_le_exp_row hp1 hp t hsample a n).trans_lt
  have he := Real.exp_lt_exp.mpr (hN a ha ht n hn)
  rw [Real.exp_log (by linarith : 0 < 1+ε)] at he
  linarith

end NLS.Fourier
