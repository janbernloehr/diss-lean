import NLS.SequenceSpaces.FiniteCoefficients
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Conjugate coefficient duality

The bilinear coefficient pairing is bounded by Hölder. Finite test sequences
of conjugate norm at most one detect the norm of every finite truncation,
and hence the norm of an arbitrary sequence at a finite exponent.
-/

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

private theorem norm_mul_le_one : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ z

/-- Bilinear coefficient duality; conjugation is incorporated into the test input. -/
def dualPairing : Coeff p →L[ℂ] Coeff q →L[ℂ] ℂ :=
  lp.dualPairing p q (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => norm_mul_le_one)

theorem dualPairing_apply (a : Coeff p) (b : Coeff q) :
    dualPairing a b = ∑' n : ℤ, a n * b n := rfl

theorem norm_dualPairing_le (a : Coeff p) (b : Coeff q) :
    ‖dualPairing a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ‖dualPairing (p := p) (q := q)‖ ≤ 1 :=
    lp.norm_dualPairing (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
      (K := 1) (fun _ => norm_mul_le_one)
  exact (dualPairing a).le_of_opNorm_le
    (by simpa using (dualPairing (p := p) (q := q)).le_of_opNorm_le h a) b

theorem dualPairing_finite_right (a : Coeff p) (b : ℤ →₀ ℂ) :
    dualPairing a (ofFinsupp (p := q) b) = b.sum (fun n z => a n * z) := by
  rw [dualPairing_apply, Finsupp.sum]
  apply tsum_eq_sum
  intro n hn
  simp [Finsupp.notMem_support_iff.mp hn]

theorem dualPairing_finite_left (a : ℤ →₀ ℂ) (b : Coeff q) :
    dualPairing (ofFinsupp (p := p) a) b = a.sum (fun n z => z * b n) := by
  rw [dualPairing_apply, Finsupp.sum]
  apply tsum_eq_sum
  intro n hn
  simp [Finsupp.notMem_support_iff.mp hn]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
private theorem norm_phase_le_one (z : ℂ) : ‖conj z / (‖z‖ : ℂ)‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [Complex.norm_real, hz]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
private theorem mul_phase (z : ℂ) : z * (conj z / (‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow,
      pow_two, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- A finite conjugate test of norm at most one realizes each truncated norm. -/
theorem exists_finite_norming_test (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (s : Finset ℤ) (a : Coeff p) :
    ∃ b : ℤ →₀ ℂ, ‖ofFinsupp (p := q) b‖ ≤ 1 ∧
      b.sum (fun n z => a n * z) = (‖truncate s a‖ : ℂ) := by
  classical
  have hpq : p.toReal.HolderConjugate q.toReal := by
    simpa using ENNReal.HolderTriple.toReal 1 hp hq
  obtain ⟨g, hg, he⟩ := (NNReal.isGreatest_Lp s (fun n => ‖a n‖₊) hpq).1
  let b : ℤ →₀ ℂ := Finsupp.onFinset s
    (fun n => if n ∈ s then (g n : ℂ) * (conj (a n) / (‖a n‖ : ℂ)) else 0)
    (by intro n hn; by_contra hs; simp [hs] at hn)
  have hb (n : ℤ) : b n =
      if n ∈ s then (g n : ℂ) * (conj (a n) / (‖a n‖ : ℂ)) else 0 := rfl
  have hbs : b.support ⊆ s := Finsupp.support_onFinset_subset
  have hbn (n : ℤ) (hn : n ∈ s) : ‖b n‖ ≤ (g n : ℝ) := by
    rw [hb, if_pos hn, norm_mul]
    calc
      _ ≤ ‖(g n : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (norm_phase_le_one _) (norm_nonneg _)
      _ = _ := by simp
  have hbnorm : ‖ofFinsupp (p := q) b‖ ≤ 1 := by
    apply lp.norm_le_of_tsum_le hq zero_le_one
    rw [tsum_eq_sum (s := s) (fun n hn => by simp [ofFinsupp_apply, hb, hn, hq.ne']), Real.one_rpow]
    calc
      _ ≤ ∑ n ∈ s, (g n : ℝ) ^ q.toReal := by
        apply Finset.sum_le_sum
        intro n hn
        exact Real.rpow_le_rpow (norm_nonneg _) (hbn n hn) hq.le
      _ ≤ 1 := by exact_mod_cast hg
  have hnorm : ‖truncate s a‖ = ∑ n ∈ s, (‖a n‖ * (g n : ℝ)) := by
    have ht : (∑' n : ℤ, ‖truncate s a n‖ ^ p.toReal) = ∑ n ∈ s, ‖a n‖ ^ p.toReal := by
      rw [tsum_eq_sum (s := s) (fun n hn => by simp [truncate_apply, hn, hp.ne'])]
      apply Finset.sum_congr rfl
      intro n hn
      rw [truncate_apply, if_pos hn]
    rw [lp.norm_eq_tsum_rpow hp, ht]
    have he' := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    simpa only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, NNReal.coe_rpow] using he'.symm
  refine ⟨b, hbnorm, ?_⟩
  rw [Finsupp.sum_of_support_subset b hbs _ (by simp), hnorm, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hb, if_pos hn, mul_left_comm, mul_phase, Complex.ofReal_mul]
  ring

omit [Fact (1 ≤ q)] in
/-- Uniform bounds against finite conjugate tests determine the full sequence norm. -/
theorem norm_le_of_finite_dual (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (hptop : p ≠ ⊤) (a : Coeff p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b : ℤ →₀ ℂ, ‖b.sum (fun n z => a n * z)‖ ≤ C * ‖ofFinsupp (p := q) b‖) :
    ‖a‖ ≤ C := by
  apply le_of_tendsto (tendsto_truncate hptop a).norm
  apply Filter.Eventually.of_forall
  intro s
  obtain ⟨b, hb, he⟩ := exists_finite_norming_test hp hq s a
  have ht := h b
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at ht
  exact ht.trans (by simpa using mul_le_mul_of_nonneg_left hb hC)

end NLS.Coeff
