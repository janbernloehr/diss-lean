import NLS.Fourier.AbsoluteSampledRows
import NLS.SequenceSpaces.CoefficientDecay

/-! # Uniform smallness of absolute sampled rows
A bounded finite block is dominated by a single fixed coefficient sequence.
Its row majorant decays, while a small input tail has a small row norm.
The tail tolerance is independent of the choice of finite block.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩

/-- Pointwise domination by two inputs transfers to the absolute row majorants. -/
theorem norm_absoluteSampledRowMajorant_le_add (hp : p ≠ ⊤) (a b c : Coeff p)
    (h : ∀ k, ‖a k‖ ≤ ‖b k‖+‖c k‖) (n : ℤ) :
    ‖absoluteSampledRowMajorant hp a n‖ ≤
      ‖absoluteSampledRowMajorant hp b n‖+‖absoluteSampledRowMajorant hp c n‖ := by
  simp only [norm_absoluteSampledRowMajorant_apply]
  rw [← mul_add,← (summable_absoluteSampledRow hp b n).tsum_add (summable_absoluteSampledRow hp c n)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (summable_absoluteSampledRow hp a n).tsum_le_tsum
    (fun k => by simpa only [add_mul] using mul_le_mul_of_nonneg_right (h k) (norm_nonneg _))
    ((summable_absoluteSampledRow hp b n).add (summable_absoluteSampledRow hp c n))

/-- Small input tails and bounded input norms give uniformly small distant absolute rows. -/
theorem exists_uniform_small_absoluteSampledRows (hp : p ≠ ⊤) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Finset ℤ, ∃ N : ℕ, ∀ a : Coeff p,
      ‖a‖ ≤ R → ‖a-Coeff.truncate s a‖ ≤ δ →
      ∀ n : ℤ, N ≤ n.natAbs → ‖absoluteSampledRowMajorant hp a n‖ < ε := by
  let C := absoluteSampledRowConstant hp
  have hC : 0 ≤ C := absoluteSampledRowConstant_nonneg hp
  let δ := ε/(2*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,fun s => ?_⟩
  let b : Coeff p := ∑ k ∈ s, lp.single p k (R : ℂ)
  have hb (k : ℤ) : b k = if k ∈ s then (R : ℂ) else 0 := by
    change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p k) (∑ j ∈ s, lp.single p j (R : ℂ)) = _
    rw [map_sum]
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  obtain ⟨N,hN⟩ := Coeff.exists_cutoff_norm_apply_lt (ENNReal.mul_ne_top (by norm_num) hp)
    (absoluteSampledRowMajorant hp b) (half_pos hε)
  refine ⟨N,fun a ha ht n hn => ?_⟩
  have hdom (k : ℤ) : ‖a k‖ ≤ ‖b k‖+‖(a-Coeff.truncate s a) k‖ := by
    by_cases hk : k ∈ s
    · simp only [hb,if_pos hk,lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,sub_self,norm_zero,add_zero,
        Complex.norm_real,Real.norm_of_nonneg hR]
      exact (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a k).trans ha
    · simp [hb,hk]
  have htail : ‖absoluteSampledRowMajorant hp (a-Coeff.truncate s a) n‖ ≤ C*δ :=
    (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ 2*p)).ne' _ n).trans
      ((norm_absoluteSampledRowMajorant_le hp _).trans (mul_le_mul_of_nonneg_left ht hC))
  have hsmall : C*δ < ε/2 := by
    have he : δ*(2*(C+1)) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  exact (norm_absoluteSampledRowMajorant_le_add hp a b _ hdom n).trans_lt
    (by linarith [hN n hn])

end NLS.Fourier
