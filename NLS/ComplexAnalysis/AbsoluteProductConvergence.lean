import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.LiminfLimsup

/-! # Absolute convergence in Appendix D

The source defines convergence by finite ordered products and permits a
zero limit. Absolute convergence of the positive norm majorants is
exactly summability of the perturbation norms; it implies genuine
convergence of the complex products without excluding zero factors.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis

/-- The positive finite product controls the entire perturbation sum. -/
theorem one_add_sum_norm_le_prod (ι : Type*) (u : ι → ℂ) (s : Finset ι) :
    1 + ∑ i ∈ s, ‖u i‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hn : 0 ≤ ∑ j ∈ s, ‖u j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1+‖u i‖ by positivity)
    nlinarith [norm_nonneg (u i)]

/-- The source's ordered absolute convergence is equivalent to an l1 perturbation. -/
theorem exists_absolute_product_limit_iff (u : ℕ → ℂ) :
    (∃ P : ℝ, Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N, (1+‖u i‖))
      atTop (𝓝 P)) ↔ Summable (fun i => ‖u i‖) := by
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨C,hC⟩ := hP.bddAbove_range
    apply summable_of_sum_range_le (fun i => norm_nonneg _) (c := C)
    intro N
    have h := one_add_sum_norm_le_prod ℕ u (Finset.range N)
    have hbound := hC (Set.mem_range_self N)
    linarith
  · intro hu
    exact ⟨_,(Real.multipliable_one_add_of_summable hu).hasProd.tendsto_prod_nat⟩

/-- The unordered absolute-product condition has the same exact criterion. -/
theorem multipliable_one_add_norm_iff {ι : Type*} (u : ι → ℂ) :
    Multipliable (fun i => 1+‖u i‖) ↔ Summable (fun i => ‖u i‖) := by
  classical
  constructor
  · intro hu
    obtain ⟨C,_,s₀,hC⟩ := hu.eventually_bounded_finsetProd
    apply summable_of_sum_le (fun i => norm_nonneg _) (c := C)
    intro s
    have h := one_add_sum_norm_le_prod ι u s
    have hm : (∏ i ∈ s, (1+‖u i‖)) ≤ ∏ i ∈ s ∪ s₀, (1+‖u i‖) :=
      Finset.prod_le_prod_of_subset_of_one_le Finset.subset_union_left
        (fun i _ => by positivity) (fun i _ _ => by simp)
    have hb := hC (s ∪ s₀) Finset.subset_union_right
    linarith
  · exact Real.multipliable_one_add_of_summable

/-- The source's absolute convergence implies actual complex convergence,
including sequences with a zero factor. -/
theorem complex_product_converges_of_absolute {u : ℕ → ℂ} {P : ℝ}
    (hP : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N, (1+‖u i‖)) atTop (𝓝 P)) :
    Multipliable (fun i => 1+u i) ∧
    Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N, (1+u i))
      atTop (𝓝 (∏' i, (1+u i))) := by
  have hs := (exists_absolute_product_limit_iff u).mp ⟨P,hP⟩
  have hp := multipliable_one_add_of_summable hs
  exact ⟨hp,hp.hasProd.tendsto_prod_nat⟩

/-- A summable perturbation has nonzero product precisely when no factor vanishes. -/
theorem tprod_one_add_ne_zero_iff {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) :
    (∏' i, (1+u i)) ≠ 0 ↔ ∀ i, 1+u i ≠ 0 := by
  constructor
  · intro h i hi
    exact h (tprod_of_exists_eq_zero ⟨i,hi⟩)
  · intro h
    exact tprod_one_add_ne_zero_of_summable h hu

/-- A zero complex product need not be absolutely convergent. -/
theorem zero_factor_ordered_product_converges :
    Tendsto (fun N : ℕ => ∏ _i ∈ Finset.range N, (1+(-1:ℂ))) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  simp [zero_pow (by omega : N ≠ 0)]

/-- The corresponding positive majorant products have no finite limit. -/
theorem zero_factor_product_not_absolute :
    ¬ ∃ P : ℝ, Tendsto (fun N : ℕ => ∏ _i ∈ Finset.range N, (1+‖(-1:ℂ)‖))
      atTop (𝓝 P) := by
  intro h
  have hs := (exists_absolute_product_limit_iff (fun _ : ℕ => (-1:ℂ))).mp h
  have hz : Tendsto (fun _ : ℕ => (1:ℝ)) cofinite (𝓝 0) := by
    simpa using hs.tendsto_cofinite_zero
  have he : (1:ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at he

/-- The positive majorant limit keeps the full sum and exponential bounds. -/
theorem absolute_product_limit_bounds {u : ℕ → ℂ} {P : ℝ}
    (hP : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N, (1+‖u i‖)) atTop (𝓝 P)) :
    1+(∑' i, ‖u i‖) ≤ P ∧ P ≤ Real.exp (∑' i, ‖u i‖) := by
  have hs := (exists_absolute_product_limit_iff u).mp ⟨P,hP⟩
  constructor
  · exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat)
      hP (fun N => one_add_sum_norm_le_prod ℕ u (Finset.range N))
  · apply le_of_tendsto_of_tendsto' hP tendsto_const_nhds
    intro N
    exact (Real.prod_one_add_le_exp_sum (Finset.range N) (fun i => norm_nonneg _)).trans
      (Real.exp_le_exp.mpr (hs.sum_le_tsum _ (fun i _ => norm_nonneg _)))

/-- Exact reindexing of the source's inclusive cutoff starting at one. -/
theorem prod_Icc_one_eq_prod_range_shift {M : Type*} [CommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∏ i ∈ Finset.Icc 1 N, f i) = ∏ i ∈ Finset.range N, f (i+1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

/-- The printed 1≤n≤N cutoffs, with the source sequence indexed from one. -/
theorem source_absolute_product_limit_iff (u : ℕ → ℂ) :
    (∃ P : ℝ, Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N, (1+‖u i‖))
      atTop (𝓝 P)) ↔ Summable (fun i => ‖u (i+1)‖) := by
  simpa only [prod_Icc_one_eq_prod_range_shift] using
    exists_absolute_product_limit_iff (fun i => u (i+1))

/-- The literal source cutoffs converge to the positive-index product and
retain both majorant bounds, without any restriction on the unused u(0). -/
theorem source_complex_product_limit_and_bounds {u : ℕ → ℂ} {P : ℝ}
    (hP : Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N, (1+‖u i‖)) atTop (𝓝 P)) :
    Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N, (1+u i))
      atTop (𝓝 (∏' i, (1+u (i+1)))) ∧
    1+(∑' i, ‖u (i+1)‖) ≤ P ∧ P ≤ Real.exp (∑' i, ‖u (i+1)‖) := by
  have h : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N, (1+‖u (i+1)‖))
      atTop (𝓝 P) := by simpa only [prod_Icc_one_eq_prod_range_shift] using hP
  refine ⟨?_,absolute_product_limit_bounds h⟩
  simpa only [prod_Icc_one_eq_prod_range_shift] using
    (complex_product_converges_of_absolute h).2

end NLS.ComplexAnalysis
