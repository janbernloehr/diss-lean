import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.LocallyBoundedAnalyticSummation

/-! # Bounds for the fixed-mode frequency series

These are the summation steps in Theorems 3.4 and 4.3. The actual spectral
estimates for the moments are separate inputs. The denominator retains the
positive Hill indices; the diagonal is treated separately.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The two quadratic-denominator kernels used in the moment estimates
are bounded by a reciprocal integer distance. -/
theorem quadratic_frequency_kernel_le (n k : ℤ) (hn : 0 < n) (hk : 0 < k)
    (hne : k ≠ n) :
    (n : ℝ)^2 / |(n : ℝ)^2 - (k : ℝ)^2| ≤ (n : ℝ) / |((n-k : ℤ) : ℝ)| ∧
      (n : ℝ)*(k : ℝ) / |(n : ℝ)^2 - (k : ℝ)^2| ≤
        (n : ℝ) / |((n-k : ℤ) : ℝ)| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : (0 : ℝ) < |((n-k : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr hne.symm
  have hfac : |(n : ℝ)^2-(k : ℝ)^2| = |((n-k : ℤ) : ℝ)| *((n : ℝ)+(k : ℝ)) := by
    rw [Int.cast_sub, ← abs_of_pos (add_pos hn' hk'), ← abs_mul]
    congr 1
    ring
  rw [hfac]
  constructor
  · apply (div_le_div_iff₀ (mul_pos hd (add_pos hn' hk')) hd).mpr
    nlinarith [mul_pos hd (mul_pos hn' hk')]
  · apply (div_le_div_iff₀ (mul_pos hd (add_pos hn' hk')) hd).mpr
    nlinarith [mul_pos hd (sq_pos_of_pos hn')]

/-- The higher polynomial factor in the Hilbert-space KdV2 estimate is
bounded for each fixed positive mode. -/
theorem hilbert_frequency_kernel_le (n k : ℤ) (hn : 0 < n) (hk : 0 < k)
    (hne : k ≠ n) :
    (n : ℝ)^2*(k : ℝ)^2 / |(n : ℝ)^2-(k : ℝ)^2| ≤
      (n : ℝ)^2*(1+(n : ℝ)^2) := by
  have hdiff : n^2-k^2 ≠ 0 := by
    intro h
    have : n = k ∨ n = -k := by
      have he : (n-k)*(n+k) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rcases this with h | h <;> omega
  have hd : 1 ≤ |(n : ℝ)^2-(k : ℝ)^2| := by
    exact_mod_cast Int.one_le_abs hdiff
  have htri : (k : ℝ)^2 ≤ |(n : ℝ)^2-(k : ℝ)^2|+(n : ℝ)^2 := by
    have := neg_le_abs ((n : ℝ)^2-(k : ℝ)^2)
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < |(n : ℝ)^2-(k : ℝ)^2|)).mpr
  nlinarith [mul_nonneg (sq_nonneg (n : ℝ))
    (show 0 ≤ (n : ℝ)^2*(|(n : ℝ)^2-(k : ℝ)^2|-1) by positivity)]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A reciprocal-distance row paired with an ℓᵖ remainder is absolutely
summable, with an ℓ¹ norm bound uniform over the remainder's norm ball. -/
theorem exists_one_coefficients_of_reciprocal_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p)
    (f : ℤ → ℂ) (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, ‖f k‖ ≤ if k = n then D else C*‖a k‖/|((n-k : ℤ) : ℝ)|) :
    ∃ b : Coeff 1, (∀ k, b k = f k) ∧
      ‖b‖ ≤ D+C*‖a‖*‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ := by
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hq1.le⟩
  let K := Coeff.reindex (Equiv.subLeft n) (Coeff.puncturedLattice p.conjExponent hq1)
  have hK (k : ℤ) : ‖a k‖*‖K k‖ =
      if k = n then 0 else ‖a k‖/|((n-k : ℤ) : ℝ)| := by
    by_cases hk : k = n
    · subst k
      simp [K]
    · simp only [K, Coeff.reindex_apply, Equiv.subLeft_apply,
        Coeff.puncturedLattice_apply, if_neg (sub_ne_zero.mpr (Ne.symm hk)),
        if_neg hk, norm_inv, Complex.norm_intCast, div_eq_mul_inv]
  obtain ⟨hs, hnorm⟩ := lp.tsum_mul_le_mul_norm
    (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) a K
  let M (k : ℤ) := (if k = n then D else 0)+C*(‖a k‖*‖K k‖)
  have hMsum : Summable M := (hasSum_ite_eq n D).summable.add (hs.mul_left C)
  have hmajor (k : ℤ) : ‖f k‖ ≤ M k := by
    have := hf k
    by_cases hk : k = n <;> simp [M, hK, hk, mul_div_assoc] at * <;> assumption
  have hfmem : Memℓp f 1 := by
    apply Coeff.memℓp_of_power_dominated f M hMsum
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hmajor
  let b : Coeff 1 := ⟨f, hfmem⟩
  refine ⟨b, fun _ => rfl, ?_⟩
  have hb : ‖b‖ ≤ ∑' k, M k := by
    have := Coeff.norm_ofFunctionOrZero_rpow_le (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      f M hMsum (by simpa only [ENNReal.toReal_one, Real.rpow_one] using hmajor)
    simpa only [ENNReal.toReal_one, Real.rpow_one,
      Coeff.ofFunctionOrZero_eq_of_coordinates f b (fun _ => rfl)] using this
  apply hb.trans
  rw [Summable.tsum_add (hasSum_ite_eq n D).summable (hs.mul_left C), tsum_ite_eq,
    tsum_mul_left]
  have hnormK : ‖K‖ = ‖Coeff.puncturedLattice p.conjExponent hq1‖ :=
    Coeff.norm_reindex _ _
  rw [hnormK] at hnorm
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Local ℓᵖ bounds for reciprocal remainders suffice for absolute convergence,
analyticity, and local uniform convergence. No continuity of the chosen
remainder sequences is required. -/
theorem analytic_tsum_of_local_reciprocal_bounds
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (f : E → ℤ → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (hb : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M D : ℝ, ∀ y ∈ V, ∃ a : Coeff p, ‖a‖ ≤ M ∧
        ∀ k, ‖f y k‖ ≤ if k = n then D else C*‖a k‖/|((n-k : ℤ) : ℝ)|) :
    (∀ x ∈ U, Summable (fun k => ‖f x k‖)) ∧
      AnalyticOnNhd ℂ (fun x => ∑' k, f x k) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, f x k)
        (fun x => ∑' k, f x k) atTop U := by
  let : Fact (1 ≤ p.conjExponent) := ⟨le_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)⟩
  apply Coeff.analytic_tsum_of_local_one_bounds f hU ha
  intro x hx
  obtain ⟨V, hV, hxV, hVU, M, D, hrows⟩ := hb x hx
  refine ⟨V, hV, hxV, hVU, D+C*M*‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖, ?_⟩
  intro y hy
  obtain ⟨a, haM, haf⟩ := hrows y hy
  obtain ⟨b, hb, hbnorm⟩ :=
    exists_one_coefficients_of_reciprocal_bound hp hp1 n a (f y) C D hC haf
  refine ⟨b, hb, hbnorm.trans ?_⟩
  gcongr

/-- The bounded-kernel alternative needed for the Hilbert-space KdV2
remainder. The diagonal is allowed an independent locally uniform bound. -/
theorem analytic_tsum_of_local_bounded_kernel_bounds
    (C : ℝ) (hC : 0 ≤ C) (n : ℤ)
    (f : E → ℤ → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (hb : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M D : ℝ, ∀ y ∈ V, ∃ a : Coeff 1, ‖a‖ ≤ M ∧
        ∀ k, ‖f y k‖ ≤ (if k = n then D else 0)+C*‖a k‖) :
    (∀ x ∈ U, Summable (fun k => ‖f x k‖)) ∧
      AnalyticOnNhd ℂ (fun x => ∑' k, f x k) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, f x k)
        (fun x => ∑' k, f x k) atTop U := by
  apply Coeff.analytic_tsum_of_local_one_bounds f hU ha
  intro x hx
  obtain ⟨V, hV, hxV, hVU, M, D, hrows⟩ := hb x hx
  refine ⟨V, hV, hxV, hVU, D+C*M, ?_⟩
  intro y hy
  obtain ⟨a, haM, haf⟩ := hrows y hy
  have hs : Summable (fun k => ‖a k‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using (lp.memℓp a).summable
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  let B (k : ℤ) := (if k = n then D else 0)+C*‖a k‖
  have hB : Summable B := (hasSum_ite_eq n D).summable.add (hs.mul_left C)
  have hmem : Memℓp (f y) 1 := Coeff.memℓp_of_power_dominated (f y) B hB
    (by simpa only [ENNReal.toReal_one, Real.rpow_one] using haf)
  let b : Coeff 1 := ⟨f y, hmem⟩
  refine ⟨b, fun _ => rfl, ?_⟩
  have hnorm := Coeff.norm_ofFunctionOrZero_rpow_le (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (f y) B hB (by simpa only [ENNReal.toReal_one, Real.rpow_one] using haf)
  simp only [ENNReal.toReal_one, Real.rpow_one,
    Coeff.ofFunctionOrZero_eq_of_coordinates (f y) b (fun _ => rfl)] at hnorm
  apply hnorm.trans
  rw [Summable.tsum_add (hasSum_ite_eq n D).summable (hs.mul_left C), tsum_ite_eq,
    tsum_mul_left]
  have hnorma : (∑' k, ‖a k‖) = ‖a‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a).symm
  rw [hnorma]
  gcongr

end NLS.KdV
