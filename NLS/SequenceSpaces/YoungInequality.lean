import NLS.SequenceSpaces.YoungFinite
import NLS.SequenceSpaces.YoungExponents
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The full discrete Young inequality

For `1 + 1/r = 1/p + 1/q`, convolution of `ℓᵖ` and `ℓᑫ` sequences is an
absolutely convergent scalar sum at every frequency and belongs to `ℓʳ`, with
constant one. Uniform finite bounds pass to the pointwise limit by the `lp`
Fatou property. All Banach endpoints, including infinity, are covered.
-/

noncomputable section
open scoped ENNReal Topology
open Filter
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

omit [Fact (1 ≤ r)] in
/-- Young-admissible inputs have absolutely convergent convolution at every frequency. -/
theorem summable_norm_youngConvolution_terms (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (n : ℤ) : Summable (fun k : ℤ => ‖a (n - k) * b k‖) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  exact summable_norm_dualPairing (reindex (Equiv.subLeft n) a)
    (exponentInclusion h.right_le_conjExponent b)

omit [Fact (1 ≤ r)] in
/-- A uniform scalar bound, including conjugate inputs with infinity output. -/
theorem norm_youngConvolution_tsum_le (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (n : ℤ) :
    ‖∑' k : ℤ, a (n - k) * b k‖ ≤ ‖a‖ * ‖b‖ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hb := norm_dualPairing_le (reindex (Equiv.subLeft n) a)
    (exponentInclusion h.right_le_conjExponent b)
  exact hb.trans (by
    rw [norm_reindex]
    exact mul_le_mul_of_nonneg_left (norm_exponentInclusion_le h.right_le_conjExponent b)
      (norm_nonneg a))

private theorem one_le_toReal {u : ℝ≥0∞} [Fact (1 ≤ u)] (hu : u ≠ ⊤) : 1 ≤ u.toReal := by
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_le_toReal ENNReal.one_ne_top hu).mpr (show 1 ≤ u from Fact.out)

/-- The finite convolution estimate for the exact Young relation, including all endpoints. -/
theorem norm_finiteConvolution_young (h : YoungRelation p q r) (a b : ℤ →₀ ℂ) :
    ‖finiteConvolution r a b‖ ≤ ‖ofFinsupp (p := p) a‖ * ‖ofFinsupp (p := q) b‖ := by
  by_cases hr₁ : r = 1
  · subst r
    have hp : p = 1 := le_antisymm h.left_le Fact.out
    have hq : q = 1 := le_antisymm h.right_le Fact.out
    subst p
    subst q
    exact norm_convolution_le _ _
  by_cases hr : r = ⊤
  · subst r
    apply lp.norm_le_of_forall_le (by positivity)
    intro n
    rw [finiteConvolution_apply]
    exact norm_youngConvolution_tsum_le h (ofFinsupp (p := p) a) (ofFinsupp (p := q) b) n
  · let : Fact (1 ≤ r.conjExponent) := ⟨ENNReal.HolderConjugate.one_le r.conjExponent r⟩
    have ht : r.conjExponent ≠ ⊤ :=
      (ENNReal.HolderConjugate.ne_top_iff_ne_one r.conjExponent r).mpr hr₁
    exact norm_finiteConvolution_le (one_le_toReal (h.left_ne_top hr))
      (one_le_toReal (h.right_ne_top hr)) (zero_lt_one.trans_le (one_le_toReal hr))
      (one_le_toReal ht) h.dual_toReal a b

/-- Restrict raw coefficients to a finite support, as a genuine finitely supported function. -/
def finiteRestriction (S : Finset ℤ) (a : ℤ → ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset S (fun n => if n ∈ S then a n else 0)
    (by intro n hn; by_contra h; simp [h] at hn)

@[simp] theorem finiteRestriction_apply (S : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) :
    finiteRestriction S a n = if n ∈ S then a n else 0 := rfl

omit [Fact (1 ≤ p)] in
@[simp] theorem ofFinsupp_finiteRestriction (S : Finset ℤ) (a : Coeff p) :
    ofFinsupp (p := p) (finiteRestriction S a) = truncate S a := by
  ext n
  simp only [ofFinsupp_apply, finiteRestriction_apply, truncate_apply]

/-- Simultaneous finite input cutoffs converge at each convolution frequency. -/
theorem tendsto_finiteConvolution_apply (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) (n : ℤ) :
    Tendsto (fun S : Finset ℤ => finiteConvolution r (finiteRestriction S a) (finiteRestriction S b) n)
      atTop (𝓝 (∑' k : ℤ, a (n - k) * b k)) := by
  simp only [finiteConvolution_apply]
  apply tendsto_tsum_of_dominated_convergence (summable_norm_youngConvolution_terms h a b n)
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({k, n - k} : Finset ℤ)] with S hS
    have hk : k ∈ S := hS (by simp)
    have hn : n - k ∈ S := hS (by simp)
    simp only [finiteRestriction_apply, if_pos hk, if_pos hn]
  · apply Eventually.of_forall
    intro S k
    by_cases hk : k ∈ S <;> by_cases hn : n - k ∈ S <;>
      simp [finiteRestriction_apply, hk, hn] <;> positivity

private theorem norm_finiteConvolution_restriction_le (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (S : Finset ℤ) :
    ‖finiteConvolution r (finiteRestriction S a) (finiteRestriction S b)‖ ≤ ‖a‖ * ‖b‖ := by
  apply (norm_finiteConvolution_young h _ _).trans
  rw [ofFinsupp_finiteRestriction, ofFinsupp_finiteRestriction]
  exact mul_le_mul (norm_truncate_le (ne_of_gt (zero_lt_one.trans_le Fact.out)) S a)
    (norm_truncate_le (ne_of_gt (zero_lt_one.trans_le Fact.out)) S b)
    (norm_nonneg _) (norm_nonneg _)

/-- Membership in the exact target exponent follows from finite Young bounds and the `lp` Fatou property. -/
theorem memlp_youngConvolution (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    Memℓp (fun n : ℤ => ∑' k : ℤ, a (n - k) * b k) r := by
  apply lp.memℓp_of_tendsto (l := atTop) (F := fun S : Finset ℤ =>
    finiteConvolution r (finiteRestriction S a) (finiteRestriction S b))
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖a‖ * ‖b‖, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact norm_finiteConvolution_restriction_le h a b S
  · exact tendsto_pi_nhds.mpr (fun n => tendsto_finiteConvolution_apply h a b n)

/-- Discrete convolution for every Banach Young triple. -/
def youngConvolution (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) : Coeff r :=
  ⟨fun n => ∑' k : ℤ, a (n - k) * b k, memlp_youngConvolution h a b⟩

@[simp] theorem youngConvolution_apply (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) (n : ℤ) :
    youngConvolution h a b n = ∑' k : ℤ, a (n - k) * b k := rfl

/-- Appendix B.2: the full Young inequality, with exact constant one and all infinity endpoints. -/
theorem norm_youngConvolution_le (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    ‖youngConvolution h a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply lp.norm_le_of_tendsto (l := atTop) (F := fun S : Finset ℤ =>
    finiteConvolution r (finiteRestriction S a) (finiteRestriction S b))
    (Eventually.of_forall (norm_finiteConvolution_restriction_le h a b))
  exact tendsto_pi_nhds.mpr (fun n => tendsto_finiteConvolution_apply h a b n)

end NLS.Coeff
