import NLS.ComplexAnalysis.HilbertWeakMovingInput
import NLS.KdV.HillFreePeriodCompactDiagonal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem tendsto_hillFreeSeparatedWeight_coordinate_of_tendsto
    {ι : Type*} {l : Filter ι} (n k : ι → ℕ) (hk : Tendsto k l atTop) (m : ℤ) :
    Tendsto (fun i => hillFreeSeparatedWeight (n i) (k i) m) l (𝓝 0) := by
  have hi : Function.Injective (fun k : ℕ => m-(k : ℤ)) := by
    intro k j he
    have hh : (k : ℤ) = (j : ℤ) := sub_right_injective he
    exact_mod_cast hh
  have ht := (Coeff.tendsto_norm_apply_cofinite (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (Coeff.puncturedLattice 2 (by norm_num))).comp hi.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at ht
  have htk := ht.comp hk
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) _
    (show Tendsto (fun i => ((Real.pi^2)⁻¹)*‖Coeff.puncturedLattice 2 (by norm_num) (m-(k i : ℤ))‖) l (𝓝 0) by
      simpa only [mul_zero, Function.comp_def] using htk.const_mul ((Real.pi^2)⁻¹))
  intro i
  have hb := hillFreeSeparatedWeightSymbol_bound (n i) (k i) m
  simpa only [hillFreeSeparatedWeight,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.shift_apply,
    norm_mul,norm_inv,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] using hb


theorem tendsto_hilbertWeightedProduct_hillFreeSeparatedWeight_of_tendsto
    {ι : Type*} {l : Filter ι} (n k : ι → ℕ) (hk : Tendsto k l atTop)
    (a : ι → Coeff 2) (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0)) :
    Tendsto (fun i => hilbertWeightedProduct (hillFreeSeparatedWeight (n i) (k i)) (a i)) l (𝓝 1) := by
  exact tendsto_hilbertWeightedProduct_of_bounded_weak_weights_of_tendsto
    (fun i => hillFreeSeparatedWeight (n i) (k i)) (2/Real.pi^2)
    (fun i => norm_hillFreeSeparatedWeight_le (n i) (k i))
    (tendsto_hillFreeSeparatedWeight_coordinate_of_tendsto n k hk) a a0 ha

/-- The free diagonal correction tends uniformly to zero on compact root
sets, allowing the deleted differential index to vary without restriction. -/
theorem exists_hilbertWeightedProduct_hillFreeSeparatedWeight_uniform_on_compact
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ J : ℕ, ∀ n k : ℕ, J≤k → ∀ a∈K,
      ‖hilbertWeightedProduct (hillFreeSeparatedWeight n k) a-1‖<ε := by
  by_contra! h
  have hw (j : ℕ) : ∃ n k : ℕ, j≤k ∧ ∃ a∈K,
      ε≤‖hilbertWeightedProduct (hillFreeSeparatedWeight n k) a-1‖ := h j
  choose n k hj a ha hbad using hw
  obtain ⟨a0,_,φ,hφ,hlim⟩ := hK.tendsto_subseq ha
  have hk : Tendsto (fun i => k (φ i)) atTop atTop :=
    (tendsto_atTop_mono hj tendsto_id).comp hφ.tendsto_atTop
  have ht := tendsto_hilbertWeightedProduct_hillFreeSeparatedWeight_of_tendsto
    (fun i => n (φ i)) (fun i => k (φ i)) hk (fun i => a (φ i)) a0 hlim
  have he : ∀ᶠ i in atTop, ‖hilbertWeightedProduct (hillFreeSeparatedWeight (n (φ i)) (k (φ i))) (a (φ i))-1‖<ε := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨i,hi⟩ := he.exists
  exact (not_lt_of_ge (hbad (φ i))) hi

theorem exists_hillFreePeriodDiagonalCorrection_uniform_tail_bound
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ a∈K, ∀ m : ℤ, J≤m.natAbs →
      ‖hillFreePeriodDiagonalCorrection n a m‖≤ε := by
  obtain ⟨J,hJ⟩ := exists_hilbertWeightedProduct_hillFreeSeparatedWeight_uniform_on_compact K hK ε hε
  refine ⟨J,?_⟩
  intro n a ha m hm
  change ‖if 0<m ∧ m≠(n : ℤ) then
    hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1 else 0‖≤ε
  split_ifs with hpos
  · exact (hJ n m.toNat (by omega) a ha).le
  · simpa only [norm_zero] using hε.le

/-- Uniform output truncation in operator norm for the original free
diagonal compact remainders, simultaneously in all deleted indices. -/
theorem exists_hillFreePeriodDiagonalCorrection_uniform_operator_tail_bound
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ a∈K,
      ‖(ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.truncateCLM (Coeff.lowFrequencies J)).comp
        (Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a))‖≤ε := by
  obtain ⟨J,hJ⟩ := exists_hillFreePeriodDiagonalCorrection_uniform_tail_bound K hK ε hε
  refine ⟨J,?_⟩
  intro n a ha
  apply ContinuousLinearMap.opNorm_le_bound _ hε.le
  intro x
  have hnorm : ‖Coeff.fourierTail J (Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a) x)‖≤
      ‖(ε : ℂ) • x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro m
    rw [Coeff.fourierTail_apply]
    by_cases hm : J≤m.natAbs
    · rw [if_pos hm]
      simpa only [Coeff.multiplierCLM_apply,Coeff.multiplier_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
        norm_real,Real.norm_eq_abs,abs_of_pos hε] using mul_le_mul_of_nonneg_right (hJ n a ha m hm) (norm_nonneg (x m))
    · rw [if_neg hm,norm_zero]
      exact norm_nonneg _
  simpa only [ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearMap.id_apply,Coeff.truncateCLM_apply,
    Coeff.fourierTail,norm_smul,norm_real,Real.norm_eq_abs,abs_of_pos hε] using hnorm

end NLS.KdV
