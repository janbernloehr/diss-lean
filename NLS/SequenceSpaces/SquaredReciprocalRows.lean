import NLS.SequenceSpaces.PowerYoung
import NLS.SequenceSpaces.ReciprocalSeries

/-!
# Reciprocal-square convolution rows for the squared-gap estimate

The sequence proof in Lemma 10.8 uses a reciprocal-square kernel and
squared gap magnitudes. Powered Young treats both sides of exponent two:
the input exponent `r = p/2` may be below one, while the powered
convolution itself is taken in Banach exponents.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- For a nonnegative family, summability of a power `0 < t ≤ 1`
implies summability of the family and bounds its sum by its `ℓᵗ` size. -/
theorem summable_and_tsum_le_power_tsum {ι : Type*} (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hpow : Summable (fun i => u i ^ t)) :
    Summable u ∧ (∑' i, u i) ≤ (∑' i, u i ^ t) ^ (1/t) := by
  classical
  have hfin (s : Finset ι) :
      (∑ i ∈ s, u i)^t ≤ ∑ i ∈ s, u i^t := by
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow ht0.ne']
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (Real.rpow_add_le_add_rpow (hu i)
        (Finset.sum_nonneg (fun j _ => hu j)) ht0.le ht1).trans
        (add_le_add_right ih _)
  have hbound (s : Finset ι) :
      (∑ i ∈ s, u i) ≤ (∑' i, u i^t)^(1/t) := by
    have hpowBound := (hfin s).trans
      (hpow.sum_le_tsum s (fun i _ => Real.rpow_nonneg (hu i) _))
    have hr := Real.rpow_le_rpow
      (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => hu i)) _)
      hpowBound (one_div_pos.mpr ht0).le
    calc
      _ = ((∑ i ∈ s, u i)^t)^(1/t) := by
        rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => hu i))]
        rw [mul_one_div_cancel ht0.ne', Real.rpow_one]
      _ ≤ _ := hr
  have hsum := summable_of_sum_le hu hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

/-- The punctured reciprocal-square kernel belongs to every exponent
strictly above one half. -/
def squaredReciprocalKernel (t : ℝ) (ht : 1/2 < t) :
    Coeff (ENNReal.ofReal t) := by
  have ht0 : 0 < t := by linarith
  let f : ℤ → ℂ := fun k => if k = 0 then 0 else
    (((|(k : ℝ)|)^(-(2 : ℝ)) : ℝ) : ℂ)
  have hs : Summable (fun k : ℤ =>
      if k = 0 then (0 : ℝ) else |(k : ℝ)|^(-(2*t))) := by
    simpa only [zero_add] using
      (ReciprocalSeries.summable_int_shifted_rpow (α := 0) le_rfl
        (by linarith : 1 < 2*t))
  have hf : Memℓp f (ENNReal.ofReal t) := by
    apply (memℓp_gen_iff (by simpa only [ENNReal.toReal_ofReal ht0.le] using ht0)).2
    apply hs.congr
    intro k
    by_cases hk : k = 0
    · simp [f, hk, ENNReal.toReal_ofReal ht0.le, Real.zero_rpow ht0.ne']
    · simp only [f, if_neg hk, ENNReal.toReal_ofReal ht0.le,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1
      ring
  exact ⟨f, hf⟩

@[simp] theorem squaredReciprocalKernel_apply (t : ℝ) (ht : 1/2 < t) (k : ℤ) :
    squaredReciprocalKernel t ht k =
      if k = 0 then 0 else (((|(k : ℝ)|)^(-(2 : ℝ)) : ℝ) : ℂ) := rfl

/-- Squared-gap convolution rows lie in the same `ℓʳ` space as their
input for every `r > 1/2`, including `r < 1`. The output is the actual
absolute row sum, not merely a formal powered convolution. -/
theorem exists_squaredReciprocalRow (r : ℝ) (hr : 1/2 < r)
    (a : Coeff (ENNReal.ofReal r)) :
    ∃ S : Coeff (ENNReal.ofReal r),
      (∀ n : ℤ,
        Summable (fun k : ℤ => ‖a (n-k) * squaredReciprocalKernel (min 1 r)
          (lt_min (by norm_num : (1/2 : ℝ) < 1) hr) k‖) ∧
        S n = ((∑' k : ℤ,
          ‖a (n-k) * squaredReciprocalKernel (min 1 r)
            (lt_min (by norm_num : (1/2 : ℝ) < 1) hr) k‖ : ℝ) : ℂ)) ∧
      ‖S‖ ≤ ‖a‖ * ‖squaredReciprocalKernel (min 1 r)
        (lt_min (by norm_num : (1/2 : ℝ) < 1) hr)‖ := by
  let t := min 1 r
  have ht : 1/2 < t := lt_min (by norm_num) hr
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < r := by linarith
  have htr : t ≤ r := min_le_right _ _
  have ht1 : t ≤ 1 := min_le_left _ _
  let b := squaredReciprocalKernel t ht
  have hrel : PowerYoungRelation r t r t :=
    ⟨ht0, htr, le_rfl, htr, by ring⟩
  obtain ⟨d, hd, hdn⟩ := Coeff.exists_powerConvolution hrel a b
  have hrow (n : ℤ) :
      Summable (fun k : ℤ => ‖a (n-k) * b k‖) ∧
      (∑' k : ℤ, ‖a (n-k) * b k‖) ≤ ‖d n‖ := by
    have hpow := Coeff.summable_powerConvolution hrel a b n
    obtain ⟨hs, hle⟩ := summable_and_tsum_le_power_tsum
      (fun k : ℤ => ‖a (n-k) * b k‖) (fun _ => norm_nonneg _) ht0 ht1 hpow
    refine ⟨hs, ?_⟩
    rw [hd n, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (tsum_nonneg (fun _ => by positivity)) _)]
    exact hle
  let S : Coeff (ENNReal.ofReal r) := ⟨
    fun n => ((∑' k : ℤ, ‖a (n-k) * b k‖ : ℝ) : ℂ),
    (lp.memℓp d).mono' (fun n => by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
      exact (hrow n).2)⟩
  refine ⟨S, ?_, ?_⟩
  · intro n
    exact ⟨(hrow n).1, rfl⟩
  · have hdom (n : ℤ) : ‖S n‖ ≤ ‖d n‖ := by
      change ‖((∑' k : ℤ, ‖a (n-k) * b k‖ : ℝ) : ℂ)‖ ≤ ‖d n‖
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
      exact (hrow n).2
    exact (lp.norm_mono (ne_of_gt (ENNReal.ofReal_pos.mpr hr0)) hdom).trans hdn

end NLS
