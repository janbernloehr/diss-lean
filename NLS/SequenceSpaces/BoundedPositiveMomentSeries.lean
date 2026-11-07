import NLS.SequenceSpaces.WeightedMomentRowBound

/-! A Hilbert majorant after one input index derivative bounds the
ENTIRE weighted positive moment series uniformly in its row index. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem positive_moment_kernel_uniform_bound (n m : ℕ+) :
    (if m=n then (1:ℝ) else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) ≤
      1+‖puncturedLattice 2 (by norm_num)‖ := by
  by_cases hmn : m=n
  · rw [if_pos hmn]
    exact le_add_of_nonneg_right (norm_nonneg _)
  · rw [if_neg hmn]
    have hd : 1/|((n:ℕ):ℝ)-(m:ℕ)| ≤ ‖puncturedLattice 2 (by norm_num)‖ := by
      rw [← norm_puncturedLattice_positive_difference (by norm_num : 1 < (2:ℝ≥0∞)) n m hmn]
      exact lp.norm_apply_le_norm (by norm_num) _ _
    have hm : (1:ℝ) ≤ (m:ℕ) := by exact_mod_cast m.pos
    have hn : (0:ℝ) < (n:ℕ) := by exact_mod_cast n.pos
    have hs : 1/((n:ℕ)+(m:ℕ):ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith

theorem norm_positive_moment_series_le_of_Hilbert_majorant
    (H : Coeff 2) (g : ℕ+ → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hH : ∀ m : ℕ+, (1+(m:ℝ))*g m ≤ ‖H ((m:ℕ):ℤ)‖)
    (u : ℕ+ → ℕ+ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n m : ℕ+, ‖u n m‖ ≤ B*(g m)^2*
      (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (n : ℕ+) :
    Summable (fun m : ℕ+ => ‖((m:ℕ):ℂ)*u n m‖) ∧
      ‖∑' m : ℕ+, ((m:ℕ):ℂ)*u n m‖ ≤
        B*(1+‖puncturedLattice 2 (by norm_num)‖)*‖H‖^2 := by
  let b := squaredGapMagnitude H
  let j : ℕ+ → ℤ := fun m => ((m:ℕ):ℤ)
  have hj : Function.Injective j := by intro a c h; exact PNat.coe_injective (Int.ofNat.inj h)
  have hb (k : ℤ) : ‖b k‖=‖H k‖^2 := by
    rw [show b k=(‖H k‖^2:ℝ) from squaredGapMagnitude_apply H k,
      Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  have hbZ : Summable (fun k : ℤ => ‖b k‖) := (lp.memℓp b).norm.summable_of_one
  have hbP : Summable (fun m : ℕ+ => ‖b (j m)‖) := hbZ.comp_injective hj
  let C := B*(1+‖puncturedLattice 2 (by norm_num)‖)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint (m : ℕ+) : ‖((m:ℕ):ℂ)*u n m‖ ≤ C*‖b (j m)‖ := by
    have hker := positive_moment_kernel_uniform_bound n m
    have hw : (m:ℝ)*(g m)^2 ≤ ‖H (j m)‖^2 := by
      have hm : (0:ℝ) ≤ (m:ℝ) := by positivity
      have hm2 : (m:ℝ) ≤ (1+(m:ℝ))^2 := by nlinarith [sq_nonneg (m:ℝ)]
      calc
        _ ≤ (1+(m:ℝ))^2*(g m)^2 := mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
        _ = ((1+(m:ℝ))*g m)^2 := by ring
        _ ≤ ‖H (j m)‖^2 := pow_le_pow_left₀ (mul_nonneg (by positivity) (hg m)) (hH m) 2
    rw [norm_mul,Complex.norm_natCast,hb]
    calc
      _ ≤ (m:ℝ)*(B*(g m)^2*(1+‖puncturedLattice 2 (by norm_num)‖)) :=
        mul_le_mul_of_nonneg_left ((hu n m).trans
          (mul_le_mul_of_nonneg_left hker (by positivity))) (by positivity)
      _ = C*((m:ℝ)*(g m)^2) := by dsimp only [C]; ring
      _ ≤ C*‖H (j m)‖^2 := mul_le_mul_of_nonneg_left hw hC
  have hs : Summable (fun m : ℕ+ => ‖((m:ℕ):ℂ)*u n m‖) :=
    (hbP.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨hs,(norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc
    _ ≤ ∑' m : ℕ+, C*‖b (j m)‖ := hs.tsum_le_tsum hpoint (hbP.mul_left C)
    _ = C*(∑' m : ℕ+, ‖b (j m)‖) := tsum_mul_left
    _ ≤ C*(∑' k : ℤ, ‖b k‖) := mul_le_mul_of_nonneg_left
      (tsum_comp_le_tsum_of_inj hbZ (fun _ => norm_nonneg _) hj) hC
    _ = C*‖H‖^2 := by
      rw [show (∑' k : ℤ, ‖b k‖)=‖b‖ by simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq,
        norm_squaredGapMagnitude]

end NLS.Coeff
