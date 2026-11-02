import NLS.KdV.FrequencySeriesBounds

/-! # Positive-index analytic frequency sums

The conclusions use the article's positive Hill indices and positive partial
sums. The hypotheses isolate the locally uniform spectral remainder bounds
still needed to instantiate these results with the actual Hill moments.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Zero extension to nonpositive integer indices preserves the positive sum. -/
theorem tsum_eq_positive_of_nonpositive_zero (f : ℤ → ℂ)
    (hf : ∀ k ≤ 0, f k = 0) : (∑' k : ℤ, f k) = ∑' k : ℕ+, f (k : ℤ) := by
  have hi : Function.Injective (fun k : ℕ+ => (k : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    change ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) at hij
    exact Int.ofNat_inj.mp hij
  apply (hi.tsum_eq ?_).symm
  intro k hk
  have hkpos : 0 < k := by
    by_contra h
    exact hk (hf k (by omega))
  refine ⟨⟨k.toNat, by omega⟩, ?_⟩
  exact Int.toNat_of_nonneg (by omega)

/-- On a zero-extended positive sequence, symmetric truncation is exactly
the positive-index partial sum, including the empty sum at `N=0`. -/
theorem sum_symmetric_eq_positive (f : ℤ → ℂ) (hf : ∀ k ≤ 0, f k = 0) (N : ℕ) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N, f k) = ∑ k ∈ Finset.Icc (1 : ℤ) N, f k := by
  apply (Finset.sum_subset ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  · intro k hk hnot
    apply hf
    simp only [Finset.mem_Icc] at hk hnot
    omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Reindexing the analytic summation conclusion gives the positive-index
series, with locally uniform convergence of its ordinary positive partial sums. -/
theorem positive_frequency_series_of_integer_series
    (f : E → ℤ → ℂ) {U : Set E}
    (hz : ∀ x ∈ U, ∀ k ≤ 0, f x k = 0)
    (hs : ∀ x ∈ U, Summable (fun k => ‖f x k‖))
    (ha : AnalyticOnNhd ℂ (fun x => ∑' k : ℤ, f x k) U)
    (hu : TendstoLocallyUniformlyOn
      (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, f x k)
      (fun x => ∑' k : ℤ, f x k) atTop U)
    (hU : IsOpen U) :
    (∀ x ∈ U, Summable (fun k : ℕ+ => ‖f x (k : ℤ)‖)) ∧
      AnalyticOnNhd ℂ (fun x => ∑' k : ℕ+, f x (k : ℤ)) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (1 : ℤ) N, f x k)
        (fun x => ∑' k : ℕ+, f x (k : ℤ)) atTop U := by
  have he (x : E) (hx : x ∈ U) := tsum_eq_positive_of_nonpositive_zero (f x) (hz x hx)
  have hi : Function.Injective (fun k : ℕ+ => (k : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    change ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) at hij
    exact Int.ofNat_inj.mp hij
  refine ⟨fun x hx => (hs x hx).comp_injective hi, ?_, ?_⟩
  · intro x hx
    apply (ha x hx).congr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he y hy
  · rw [Metric.tendstoLocallyUniformlyOn_iff] at hu ⊢
    intro ε hε x hx
    obtain ⟨V, hV, hbound⟩ := hu ε hε x hx
    refine ⟨V ∩ U, inter_mem hV self_mem_nhdsWithin, hbound.mono ?_⟩
    intro N hN y hy
    simpa only [he y hy.2, sum_symmetric_eq_positive (f y) (hz y hy.2) N] using hN y hy.1

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The quadratic-denominator estimates for the KdV moments and the
non-Hilbert KdV2 moments imply absolute and locally uniform convergence
to an analytic positive-index series. The maximum permits either numerator
`n²` (Theorem 3.4) or `n*k` (the second case of Theorem 4.3). -/
theorem analytic_positive_series_of_quadratic_bounds
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (hn : 0 < n)
    (f : E → ℤ → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (hz : ∀ x ∈ U, ∀ k ≤ 0, f x k = 0)
    (hb : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M D : ℝ, ∀ y ∈ V, ∃ a : Coeff p, ‖a‖ ≤ M ∧
        ∀ k, 0 < k → ‖f y k‖ ≤ if k = n then D else
          max ((n : ℝ)^2 / |(n : ℝ)^2-(k : ℝ)^2|)
            ((n : ℝ)*(k : ℝ) / |(n : ℝ)^2-(k : ℝ)^2|)*‖a k‖) :
    (∀ x ∈ U, Summable (fun k : ℕ+ => ‖f x (k : ℤ)‖)) ∧
      AnalyticOnNhd ℂ (fun x => ∑' k : ℕ+, f x (k : ℤ)) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (1 : ℤ) N, f x k)
        (fun x => ∑' k : ℕ+, f x (k : ℤ)) atTop U := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb' : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M D : ℝ, ∀ y ∈ V, ∃ a : Coeff p, ‖a‖ ≤ M ∧
        ∀ k, ‖f y k‖ ≤ if k = n then D else (n : ℝ)*‖a k‖/|((n-k : ℤ) : ℝ)| := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU, M, D, hrows⟩ := hb x hx
    refine ⟨V, hV, hxV, hVU, M, D, ?_⟩
    intro y hy
    obtain ⟨a, haM, haf⟩ := hrows y hy
    refine ⟨a, haM, ?_⟩
    intro k
    by_cases hk : 0 < k
    · by_cases hkn : k = n
      · simpa only [if_pos hkn] using haf k hk
      · have hker := quadratic_frequency_kernel_le n k hn hk hkn
        have hf := haf k hk
        simp only [if_neg hkn] at hf ⊢
        apply hf.trans
        calc
          _ ≤ ((n : ℝ)/|((n-k : ℤ) : ℝ)|)*‖a k‖ :=
            mul_le_mul_of_nonneg_right (max_le hker.1 hker.2) (norm_nonneg (a k))
          _ = _ := by ring
    · have hkn : k ≠ n := by omega
      rw [hz y (hVU hy) k (by omega), norm_zero, if_neg hkn]
      positivity
  obtain ⟨hs, hsum, hlocal⟩ :=
    analytic_tsum_of_local_reciprocal_bounds hp hp1 n (n : ℝ) hn'.le f hU ha hb'
  exact positive_frequency_series_of_integer_series f hz hs hsum hlocal hU

/-- The Hilbert-space KdV2 polynomial kernel also gives an analytic
positive-index sum under the source's locally bounded ℓ¹ remainders. -/
theorem analytic_positive_series_of_hilbert_bounds
    (n : ℤ) (hn : 0 < n) (f : E → ℤ → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (hz : ∀ x ∈ U, ∀ k ≤ 0, f x k = 0)
    (hb : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M D : ℝ, ∀ y ∈ V, ∃ a : Coeff 1, ‖a‖ ≤ M ∧
        ∀ k, 0 < k → ‖f y k‖ ≤ if k = n then D else
          ((n : ℝ)^2*(k : ℝ)^2 / |(n : ℝ)^2-(k : ℝ)^2|)*‖a k‖) :
    (∀ x ∈ U, Summable (fun k : ℕ+ => ‖f x (k : ℤ)‖)) ∧
      AnalyticOnNhd ℂ (fun x => ∑' k : ℕ+, f x (k : ℤ)) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (1 : ℤ) N, f x k)
        (fun x => ∑' k : ℕ+, f x (k : ℤ)) atTop U := by
  have hC : 0 ≤ (n : ℝ)^2*(1+(n : ℝ)^2) := by positivity
  have hb' : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M D : ℝ, ∀ y ∈ V, ∃ a : Coeff 1, ‖a‖ ≤ M ∧
        ∀ k, ‖f y k‖ ≤ (if k = n then D else 0)+
          ((n : ℝ)^2*(1+(n : ℝ)^2))*‖a k‖ := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU, M, D, hrows⟩ := hb x hx
    refine ⟨V, hV, hxV, hVU, M, D, ?_⟩
    intro y hy
    obtain ⟨a, haM, haf⟩ := hrows y hy
    refine ⟨a, haM, ?_⟩
    intro k
    by_cases hk : 0 < k
    · by_cases hkn : k = n
      · have hf := haf k hk
        simp only [if_pos hkn] at hf ⊢
        exact hf.trans (le_add_of_nonneg_right (mul_nonneg hC (norm_nonneg _)))
      · have hf := haf k hk
        simp only [if_neg hkn, zero_add] at hf ⊢
        exact hf.trans (mul_le_mul_of_nonneg_right
          (hilbert_frequency_kernel_le n k hn hk hkn) (norm_nonneg _))
    · rw [hz y (hVU hy) k (by omega), norm_zero, if_neg (show k ≠ n by omega)]
      positivity
  obtain ⟨hs, hsum, hlocal⟩ := analytic_tsum_of_local_bounded_kernel_bounds
    ((n : ℝ)^2*(1+(n : ℝ)^2)) hC n f hU ha hb'
  exact positive_frequency_series_of_integer_series f hz hs hsum hlocal hU

end NLS.KdV
