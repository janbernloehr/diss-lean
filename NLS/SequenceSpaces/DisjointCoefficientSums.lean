import NLS.SequenceSpaces.Truncation

/-! # Exact power norms of finite disjoint coefficient sums -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Disjoint coordinate supports make the pth power of the norm additive. -/
theorem norm_sum_rpow_of_disjoint {ι : Type*} (hp : 0 < p.toReal)
    (s : Finset ι) (x : ι → Coeff p)
    (hd : (s : Set ι).Pairwise (fun i j => Disjoint (Function.support (x i)) (Function.support (x j)))) :
    ‖∑ i ∈ s, x i‖ ^ p.toReal = ∑ i ∈ s, ‖x i‖ ^ p.toReal := by
  classical
  have hpoint (n : ℤ) : ‖(∑ i ∈ s, x i) n‖ ^ p.toReal = ∑ i ∈ s, ‖x i n‖ ^ p.toReal := by
    change ‖(lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n) (∑ i ∈ s, x i)‖ ^ p.toReal = _
    rw [map_sum]
    simp only [lp.evalₗ_apply]
    by_cases h : ∃ i ∈ s, x i n ≠ 0
    · obtain ⟨i,hi,hin⟩ := h
      have hj (j : ι) (hjs : j ∈ s) (hji : j ≠ i) : x j n = 0 := by
        by_contra hjn
        exact Set.disjoint_left.mp (hd hi hjs hji.symm) hin hjn
      rw [Finset.sum_eq_single i (fun j hjs hji => hj j hjs hji) (by simp [hi]),
        Finset.sum_eq_single i (fun j hjs hji => by simp [hj j hjs hji,hp.ne']) (by simp [hi])]
    · have hz : ∀ i ∈ s, x i n = 0 := by simpa using h
      simp only [Finset.sum_eq_zero hz,norm_zero,Real.zero_rpow hp.ne']
      exact (Finset.sum_eq_zero (fun i hi => by simp [hz i hi,hp.ne'])).symm
  rw [lp.norm_rpow_eq_tsum hp]
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun i _ => (lp.memℓp (x i)).summable hp)]
  simp_rw [← lp.norm_rpow_eq_tsum hp]

/-- Uniform bounds on disjoint blocks give cardinality to the power 1/p growth. -/
theorem norm_sum_le_card_rpow_of_disjoint {ι : Type*} (hp : 0 < p.toReal)
    (s : Finset ι) (x : ι → Coeff p)
    (hd : (s : Set ι).Pairwise (fun i j => Disjoint (Function.support (x i)) (Function.support (x j))))
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ i ∈ s, ‖x i‖ ≤ M) :
    ‖∑ i ∈ s, x i‖ ≤ (s.card : ℝ) ^ (1/p.toReal)*M := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp).mp
  rw [norm_sum_rpow_of_disjoint hp s x hd,Real.mul_rpow (by positivity) hM,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ s.card)]
  simp only [one_div_mul_cancel hp.ne',Real.rpow_one]
  calc
    ∑ i ∈ s, ‖x i‖ ^ p.toReal ≤ ∑ _i ∈ s, M ^ p.toReal :=
      Finset.sum_le_sum (fun i hi => Real.rpow_le_rpow (norm_nonneg _) (hx i hi) hp.le)
    _ = (s.card : ℝ)*M ^ p.toReal := by simp

/-- Uniform lower bounds on disjoint blocks give the matching growth from below. -/
theorem card_rpow_mul_le_norm_sum_of_disjoint {ι : Type*} (hp : 0 < p.toReal)
    (s : Finset ι) (x : ι → Coeff p)
    (hd : (s : Set ι).Pairwise (fun i j => Disjoint (Function.support (x i)) (Function.support (x j))))
    {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ i ∈ s, δ ≤ ‖x i‖) :
    (s.card : ℝ) ^ (1/p.toReal)*δ ≤ ‖∑ i ∈ s, x i‖ := by
  apply (Real.rpow_le_rpow_iff (by positivity) (norm_nonneg _) hp).mp
  rw [norm_sum_rpow_of_disjoint hp s x hd,Real.mul_rpow (by positivity) hδ,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ s.card)]
  simp only [one_div_mul_cancel hp.ne',Real.rpow_one]
  calc
    (s.card : ℝ)*δ ^ p.toReal = ∑ _i ∈ s, δ ^ p.toReal := by simp
    _ ≤ ∑ i ∈ s, ‖x i‖ ^ p.toReal :=
      Finset.sum_le_sum (fun i hi => Real.rpow_le_rpow hδ (hx i hi) hp.le)

end NLS.Coeff
