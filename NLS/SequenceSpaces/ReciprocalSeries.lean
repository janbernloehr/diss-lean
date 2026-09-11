import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Real.ConjExponents

/-!
# Quantitative reciprocal-power series estimates

Appendix B, Lemma B.1, supplies the numerical constants in the resolvent
estimates of Chapter 1, Lemmas 3.2 and 3.4. We use real exponents and prove
the integral comparison, the two stated bounds, and translated tail estimates.
-/

noncomputable section
open Set Real MeasureTheory Filter Topology

namespace NLS.ReciprocalSeries

private theorem antitone_shifted_rpow {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) :
    AntitoneOn (fun x : ℝ => (x + β) ^ (-q)) (Ici 0) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (by linarith [mem_Ici.mp hx])
    (by linarith) (by linarith)

private theorem integral_shifted_rpow {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) :
    (∫ x : ℝ in Ioi 0, (x + β) ^ (-q)) = β ^ (1 - q) / (q - 1) := by
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t + β) ^ (1 - q) / (1 - q)) ((x + β) ^ (-q)) x := by
    intro x hx
    convert! (((hasDerivAt_id x).add_const β).rpow_const (p := 1 - q)
      (by left; change x + β ≠ 0; linarith [mem_Ici.mp hx])).div_const (1 - q) using 1
    simp only [id_eq, one_mul, show 1 - q - 1 = -q by ring,
        mul_div_cancel_left₀ _ (show 1 - q ≠ 0 by linarith)]
  have ht : Tendsto (fun t : ℝ => (t + β) ^ (1 - q) / (1 - q)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < q - 1)).comp
      (tendsto_atTop_add_const_right atTop β tendsto_id)
    simpa only [neg_sub, zero_div, Function.comp_apply, id_eq] using h.div_const (1 - q)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (integrableOn_add_rpow_Ioi_of_lt (by linarith : -q < -1) (by linarith : -β < 0)) ht
  have he : 1 - q = -(q - 1) := by ring
  simpa only [zero_add, zero_sub, he, div_neg, neg_neg] using hi

/-- A shifted reciprocal-power series is summable whenever the exponent exceeds one. -/
theorem summable_nat_shifted_rpow {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) :
    Summable (fun n : ℕ => ((n : ℝ) + β) ^ (-q)) :=
  (antitone_shifted_rpow hβ hq).summable_of_integrableOn_Ioi_zero
    (integrableOn_add_rpow_Ioi_of_lt (by linarith) (by linarith))
    (fun x hx => Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)

/-- Integral-test bound, retaining the initial summand. -/
theorem tsum_nat_shifted_rpow_le {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) :
    (∑' n : ℕ, ((n : ℝ) + β) ^ (-q)) ≤ β ^ (-q) + β ^ (1 - q) / (q - 1) := by
  have h := (antitone_shifted_rpow hβ hq).tsum_le_integral
    (integrableOn_add_rpow_Ioi_of_lt (by linarith) (by linarith))
    (fun x hx => Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)
  simpa only [zero_add, integral_shifted_rpow hβ hq] using h

/-- Appendix B.1, first bound, written with the reciprocal exponent `q`. -/
theorem tsum_nat_succ_shifted_rpow_le {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) :
    (∑' n : ℕ, (α + (n + 1 : ℝ)) ^ (-q)) ≤
      (q + α) / (q - 1) * (1 + α) ^ (-q) := by
  have hβ : 0 < 1 + α := by linarith
  have he : (1 + α) ^ (1 - q) = (1 + α) * (1 + α) ^ (-q) := by
    rw [sub_eq_add_neg, Real.rpow_add hβ, Real.rpow_one]
  have h := tsum_nat_shifted_rpow_le hβ hq
  have hf : (fun n : ℕ => (n + (1 + α)) ^ (-q)) =
      (fun n : ℕ => (α + (n + 1 : ℝ)) ^ (-q)) := by
    funext n
    congr 1
    ring
  rw [hf, he] at h
  convert h using 1
  field_simp [show q - 1 ≠ 0 by linarith]
  ring

/-- The explicit first bound is at most the simpler conjugate-exponent bound. -/
theorem shifted_rpow_bound_le_simple {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) :
    (q + α) / (q - 1) * (1 + α) ^ (-q) ≤
      q / (q - 1) * (1 + α) ^ (1 - q) := by
  have hβ : 0 < 1 + α := by linarith
  rw [show 1 - q = 1 + -q by ring, Real.rpow_add hβ, Real.rpow_one]
  have hcoeff : (q + α) / (q - 1) ≤ q / (q - 1) * (1 + α) := by
    calc
      _ ≤ (q * (1 + α)) / (q - 1) :=
        div_le_div_of_nonneg_right (by nlinarith) (by linarith)
      _ = _ := by ring
  nlinarith [Real.rpow_pos_of_pos hβ (-q)]

/-- Appendix B.1, second bound, still expressed in terms of `q`. -/
theorem tsum_nat_succ_shifted_rpow_le_simple {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) :
    (∑' n : ℕ, (α + (n + 1 : ℝ)) ^ (-q)) ≤
      q / (q - 1) * (1 + α) ^ (1 - q) :=
  (tsum_nat_succ_shifted_rpow_le hα hq).trans (shifted_rpow_bound_le_simple hα hq)

/-- Appendix B.1 in the dissertation's conjugate-exponent notation. -/
theorem shifted_reciprocal_series_bounds {α p q : ℝ} (hα : 0 ≤ α)
    (hpq : p.HolderConjugate q) :
    (∑' n : ℕ, 1 / (α + (n + 1 : ℝ)) ^ q) ≤
        (q + α) / (q - 1) / (1 + α) ^ q ∧
      (q + α) / (q - 1) / (1 + α) ^ q ≤ p / (1 + α) ^ (q - 1) := by
  have he : (fun n : ℕ => 1 / (α + (n + 1 : ℝ)) ^ q) =
      (fun n : ℕ => (α + (n + 1 : ℝ)) ^ (-q)) := by
    funext n
    rw [Real.rpow_neg (by positivity), one_div]
  rw [he]
  constructor
  · simpa only [Real.rpow_neg (by positivity : 0 ≤ 1 + α), div_eq_mul_inv]
      using tsum_nat_succ_shifted_rpow_le hα hpq.symm.lt
  · have h := shifted_rpow_bound_le_simple hα hpq.symm.lt
    rw [← hpq.symm.conjugate_eq] at h
    simpa only [show 1 - q = -(q - 1) by ring,
      Real.rpow_neg (by positivity : 0 ≤ 1 + α), div_eq_mul_inv] using h

/-- A tail starting after `N` is bounded by the integral starting at `α + N`. -/
theorem tsum_nat_tail_shifted_rpow_le {α q : ℝ} (hq : 1 < q) (N : ℕ)
    (hαN : 0 < α + N) :
    (∑' k : ℕ, (α + (k + N + 1 : ℝ)) ^ (-q)) ≤
      (α + N) ^ (1 - q) / (q - 1) := by
  have h := (antitone_shifted_rpow hαN hq).tsum_add_one_le_integral
    (integrableOn_add_rpow_Ioi_of_lt (by linarith) (by linarith))
    (fun x hx => Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)
  rw [integral_shifted_rpow hαN hq] at h
  convert h using 1
  congr 1
  funext k
  push_cast
  congr 1
  ring

private theorem punctured_pos (α q : ℝ) (n : ℕ) :
    (if (n : ℤ) + 1 = 0 then 0 else (α + |(((n : ℤ) + 1 : ℤ) : ℝ)|) ^ (-q)) =
      (α + (n + 1 : ℝ)) ^ (-q) := by
  rw [if_neg (by omega)]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]

private theorem punctured_neg (α q : ℝ) (n : ℕ) :
    (if -((n : ℤ) + 1) = 0 then 0 else (α + |((-((n : ℤ) + 1) : ℤ) : ℝ)|) ^ (-q)) =
      (α + (n + 1 : ℝ)) ^ (-q) := by
  rw [if_neg (by omega)]
  simp only [Int.cast_neg, abs_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]

/-- Summability on the full integer lattice, with the central term omitted. -/
theorem summable_int_shifted_rpow {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) :
    Summable (fun m : ℤ => if m = 0 then 0 else (α + |(m : ℝ)|) ^ (-q)) := by
  have h := summable_nat_shifted_rpow (by linarith : 0 < 1 + α) hq
  have hs : Summable (fun n : ℕ => (α + (n + 1 : ℝ)) ^ (-q)) := by
    convert h using 1
    funext n
    congr 1
    ring
  apply Summable.of_add_one_of_neg_add_one
  · simpa only [punctured_pos] using hs
  · simpa only [punctured_neg] using hs

/-- The punctured integer lattice is the union of two identical one-sided series. -/
theorem tsum_int_shifted_rpow_eq_two_mul {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) :
    (∑' m : ℤ, if m = 0 then 0 else (α + |(m : ℝ)|) ^ (-q)) =
      2 * ∑' n : ℕ, (α + (n + 1 : ℝ)) ^ (-q) := by
  have hs := summable_int_shifted_rpow hα hq
  have hpos := hs.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (by
    intro a b hab
    dsimp only at hab
    omega)
  have hneg := hs.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (by
    intro a b hab
    dsimp only at hab
    omega)
  rw [tsum_of_add_one_of_neg_add_one
    (f := fun m : ℤ => if m = 0 then 0 else (α + |(m : ℝ)|) ^ (-q)) hpos hneg]
  simp only [punctured_pos, punctured_neg, ite_true, add_zero]
  ring

/-- Bilateral form of Appendix B.1 for a punctured reciprocal lattice. -/
theorem tsum_int_shifted_rpow_le {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) :
    (∑' m : ℤ, if m = 0 then 0 else (α + |(m : ℝ)|) ^ (-q)) ≤
      2 * (q / (q - 1)) * (1 + α) ^ (1 - q) := by
  rw [tsum_int_shifted_rpow_eq_two_mul hα hq]
  have h := tsum_nat_succ_shifted_rpow_le_simple hα hq
  linarith

/-- The positive-shift lattice estimate used for the height-dependent resolvent bound. -/
theorem tsum_int_shifted_rpow_le_integral {α q : ℝ} (hα : 0 < α) (hq : 1 < q) :
    (∑' m : ℤ, if m = 0 then 0 else (α + |(m : ℝ)|) ^ (-q)) ≤
      2 / (q - 1) * α ^ (1 - q) := by
  rw [tsum_int_shifted_rpow_eq_two_mul hα.le hq]
  have h := tsum_nat_tail_shifted_rpow_le hq 0 (by simpa using hα)
  simp only [Nat.cast_zero, add_zero] at h
  calc
    _ ≤ 2 * (α ^ (1 - q) / (q - 1)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- The same lattice estimate holds around any Fourier frequency. -/
theorem tsum_int_centered_shifted_rpow_le {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) (n : ℤ) :
    (∑' m : ℤ, if m = n then 0 else (α + |((m - n : ℤ) : ℝ)|) ^ (-q)) ≤
      2 * (q / (q - 1)) * (1 + α) ^ (1 - q) := by
  have he := (Equiv.subRight n).tsum_eq
    (fun m : ℤ => if m = 0 then (0 : ℝ) else (α + |(m : ℝ)|) ^ (-q))
  simp only [Equiv.subRight_apply, sub_eq_zero] at he
  rw [he]
  exact tsum_int_shifted_rpow_le hα hq

end NLS.ReciprocalSeries
