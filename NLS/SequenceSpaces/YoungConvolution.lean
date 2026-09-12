import NLS.SequenceSpaces.YoungInequality
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous bilinear convolution for every Young triple

The general convolution agrees with the previous `ℓ¹`-factor construction,
commutes with swapping its inputs, and has the expected single-mode action.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Additivity in the first input follows from absolute convergence at each frequency. -/
theorem youngConvolution_add_left (h : YoungRelation p q r) (a a' : Coeff p) (b : Coeff q) :
    youngConvolution h (a + a') b = youngConvolution h a b + youngConvolution h a' b := by
  ext n
  simp only [youngConvolution_apply, lp.coeFn_add, Pi.add_apply, add_mul]
  exact (summable_norm_youngConvolution_terms h a b n).of_norm.tsum_add
    (summable_norm_youngConvolution_terms h a' b n).of_norm

theorem youngConvolution_add_right (h : YoungRelation p q r) (a : Coeff p) (b b' : Coeff q) :
    youngConvolution h a (b + b') = youngConvolution h a b + youngConvolution h a b' := by
  ext n
  simp only [youngConvolution_apply, lp.coeFn_add, Pi.add_apply, mul_add]
  exact (summable_norm_youngConvolution_terms h a b n).of_norm.tsum_add
    (summable_norm_youngConvolution_terms h a b' n).of_norm

theorem youngConvolution_smul_left (h : YoungRelation p q r) (c : ℂ) (a : Coeff p) (b : Coeff q) :
    youngConvolution h (c • a) b = c • youngConvolution h a b := by
  ext n
  simp only [youngConvolution_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    tsum_mul_left]

theorem youngConvolution_smul_right (h : YoungRelation p q r) (c : ℂ) (a : Coeff p) (b : Coeff q) :
    youngConvolution h a (c • b) = c • youngConvolution h a b := by
  ext n
  simp only [youngConvolution_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

/-- General Young convolution as a continuous complex bilinear map, with norm at most one. -/
def youngConvolutionCLM (h : YoungRelation p q r) : Coeff p →L[ℂ] Coeff q →L[ℂ] Coeff r :=
  (LinearMap.mk₂ ℂ (youngConvolution h) (youngConvolution_add_left h)
    (youngConvolution_smul_left h) (youngConvolution_add_right h) (youngConvolution_smul_right h)).mkContinuous₂
    1 (fun a b => by simpa only [one_mul, LinearMap.mk₂_apply] using norm_youngConvolution_le h a b)

@[simp] theorem youngConvolutionCLM_apply (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    youngConvolutionCLM h a b = youngConvolution h a b := rfl

theorem norm_youngConvolutionCLM_le (h : YoungRelation p q r) : ‖youngConvolutionCLM h‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- The full construction is commutative, with the input exponents exchanged. -/
theorem youngConvolution_comm (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    youngConvolution h a b = youngConvolution h.symm b a := by
  ext n
  rw [youngConvolution_apply, youngConvolution_apply,
    ← (Equiv.subLeft n).tsum_eq (fun k : ℤ => b (n - k) * a k)]
  apply tsum_congr
  intro k
  simp only [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

/-- Compatibility with the original `ℓ¹`-factor Banach-series construction. -/
theorem youngConvolution_eq_convolution (h : YoungRelation p 1 p) (a : Coeff p) (b : Coeff 1) :
    youngConvolution h a b = convolution a b := by
  ext n
  exact (convolution_apply a b n).symm

/-- A single right frequency shifts the first input, including its exponent embedding. -/
theorem youngConvolution_single_right (h : YoungRelation p q r) (a : Coeff p) (k : ℤ) (c : ℂ) :
    youngConvolution h a (lp.single q k c) = c • shift k (exponentInclusion h.left_le a) := by
  ext n
  simp [youngConvolution_apply, lp.single_apply, Pi.single_apply, mul_comm]

/-- A single left frequency shifts the second input with the same scalar amplitude. -/
theorem youngConvolution_single_left (h : YoungRelation p q r) (b : Coeff q) (k : ℤ) (c : ℂ) :
    youngConvolution h (lp.single p k c) b = c • shift k (exponentInclusion h.right_le b) := by
  rw [youngConvolution_comm]
  exact youngConvolution_single_right h.symm b k c

/-- The unit bound is attained by unit single modes, so the bilinear constant is sharp. -/
theorem norm_youngConvolutionCLM (h : YoungRelation p q r) : ‖youngConvolutionCLM h‖ = 1 := by
  apply le_antisymm (norm_youngConvolutionCLM_le h)
  have hb := (youngConvolutionCLM h).le_opNorm₂ (lp.single p 0 1) (lp.single q 0 1)
  have he : youngConvolutionCLM h (lp.single p 0 1) (lp.single q 0 1) = lp.single r 0 1 := by
    ext n
    simp [youngConvolution_apply, lp.single_apply, Pi.single_apply]
  rw [he] at hb
  simpa [lp.norm_single (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)),
    lp.norm_single (zero_lt_one.trans_le (show 1 ≤ q from Fact.out)),
    lp.norm_single (zero_lt_one.trans_le (show 1 ≤ r from Fact.out))] using hb

/-- Joint continuity in both coefficient norms for any Young triple. -/
theorem continuous_youngConvolution (h : YoungRelation p q r) :
    Continuous (fun ab : Coeff p × Coeff q => youngConvolution h ab.1 ab.2) :=
  (((youngConvolutionCLM h).continuous.comp continuous_fst).clm_apply continuous_snd)

/-- Arbitrary converging input approximations give convergence in the full output norm. -/
theorem tendsto_youngConvolution (h : YoungRelation p q r) {ι : Type*} {l : Filter ι}
    {aᵢ : ι → Coeff p} {bᵢ : ι → Coeff q} {a : Coeff p} {b : Coeff q}
    (ha : Filter.Tendsto aᵢ l (nhds a)) (hb : Filter.Tendsto bᵢ l (nhds b)) :
    Filter.Tendsto (fun i => youngConvolution h (aᵢ i) (bᵢ i)) l (nhds (youngConvolution h a b)) := by
  have hpair : Filter.Tendsto (fun i => (aᵢ i, bᵢ i)) l (nhds (a, b)) := ha.prodMk_nhds hb
  simpa only [Function.comp_def] using!
    ((continuous_youngConvolution h).tendsto (a, b)).comp hpair

/-- Finite input cutoffs converge in output norm whenever both input exponents are finite,
including the conjugate-input case with infinity output. -/
theorem tendsto_youngConvolution_truncate (h : YoungRelation p q r) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (a : Coeff p) (b : Coeff q) :
    Filter.Tendsto (fun S : Finset ℤ => youngConvolution h (truncate S a) (truncate S b))
      Filter.atTop (nhds (youngConvolution h a b)) :=
  tendsto_youngConvolution h (tendsto_truncate hp a) (tendsto_truncate hq b)

end NLS.Coeff
