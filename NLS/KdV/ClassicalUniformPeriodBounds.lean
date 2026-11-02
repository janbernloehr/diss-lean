import NLS.KdV.ClassicalUniformPrimitiveBounds
import NLS.KdV.ClassicalPeriodIntegrationByParts

/-! # An actual uniform summable bound on the off-diagonal period tail

The primitive input in the previous scalar estimate is discharged using
the actual uniform source-continuation bounds. The resulting reciprocal
square frequency kernel is uniform on a single potential neighborhood.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem positiveIndex_squared_energy_kernel_le (n k : ℕ+) (hnk : n ≠ k) :
    (n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2 ≤
      1/(4*|(k : ℝ)-(n : ℝ)|^2) := by
  have hne : (k : ℝ) ≠ (n : ℝ) := by
    intro he
    apply hnk
    exact_mod_cast he.symm
  have hd : (k : ℝ)-(n : ℝ) ≠ 0 := sub_ne_zero.mpr hne
  have hs : (k : ℝ)^2-(n : ℝ)^2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by positivity) hd
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hs))
    (mul_pos (by norm_num) (sq_pos_of_ne_zero (abs_ne_zero.mpr hd)))).mpr
  rw [one_mul,sq_abs,sq_abs]
  nlinarith [sq_nonneg (((k : ℝ)-(n : ℝ))^2)]

/-- No uniform primitive-bound assumption is supplied: it is proved for
the actual continuation before the two tail indices are chosen. This is
an entry estimate; bounded-operator construction remains separate. -/
theorem exists_classicalHill_uniform_offDiagonal_period_bound :
    ∃ N M : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), ∃ K : ℝ,
      0 < N ∧ N ≤ M ∧ IsOpen V ∧ 0 ∈ V ∧ 0 < K ∧
      (∀ n k : ℕ+, AnalyticOnNhd ℂ (classicalHillUniformPeriod N n k) V ∧
        classicalHillUniformPeriod N n k 0 = if n = k then 1 else 0) ∧
      ∀ n k : ℕ+, M < (n : ℕ) → M < (k : ℕ) → n ≠ k → ∀ q ∈ V,
        ‖classicalHillUniformPeriod N n k q‖ ≤ K/|(k : ℝ)-(n : ℝ)|^2 := by
  obtain ⟨N,M,W,hN,hNM,hW,h0W,hentries,hfactor,htail⟩ :=
    exists_classicalHill_uniform_period_tail_formula
  obtain ⟨R,C,hR,_,hC,hprim⟩ := exists_classicalHill_uniform_contour_primitive_bounds
  let A : ℝ := Real.pi/4+C*R
  have hA : 0 < A := by dsimp only [A]; positivity
  let K : ℝ := (5/Real.pi)*A
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨N,M,W ∩ ball 0 R,K,hN,hNM,hW.inter isOpen_ball,⟨h0W,mem_ball_self hR⟩,hK,
    fun n k => ⟨(hentries n k).1.mono inter_subset_left,(hentries n k).2⟩,?_⟩
  intro n k hn hk hnk q hq
  have hqR : ‖q‖ < R := by simpa only [mem_ball,dist_zero_right] using hq.2
  have hbound := norm_classicalHillUniformHighPeriod_le N n k hnk q (I*(k : ℂ)*Real.pi) A hA.le
    (hfactor n q hq.1) (fun z hz => (hprim q hqR k z hz).1)
    (htail n k hn hk hnk q hq.1).1 (fun z hz =>
      (hprim q hqR k z hz).2.2.2.trans (by dsimp only [A]; nlinarith))
  have hkN : ¬ (k : ℕ) ≤ N := Nat.not_le_of_gt (hNM.trans_lt hk)
  rw [classicalHillUniformPeriod,if_neg hkN]
  calc
    _ ≤ ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
      convert hbound using 1
      ring
    _ ≤ ((20/Real.pi)*A)*(1/(4*|(k : ℝ)-(n : ℝ)|^2)) :=
      mul_le_mul_of_nonneg_left (positiveIndex_squared_energy_kernel_le n k hnk) (by positivity)
    _ = K/|(k : ℝ)-(n : ℝ)|^2 := by dsimp only [K]; ring

end NLS.KdV
