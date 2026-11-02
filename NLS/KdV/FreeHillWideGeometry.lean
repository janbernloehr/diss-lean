import NLS.KdV.FreeHill

/-!
# Wide Hill lattice geometry independent of the potential

These shared lattice and covering proofs are reused from the regular Hill
branch. No regular-potential spectral conclusion is imported. The wider
radius12n strips require n>=2 and cover the high real half-line.
-/
noncomputable section
open Set Metric
namespace NLS.KdV

/-- A separate, wider region, used only with n >= 2. -/
def wideHillStrip (n : ℕ) : Set ℂ :=
  {z | |z.re-freeHillValue n| ≤ 12*(n : ℝ)}

theorem freeHill_denominator_lower_wide {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : z ∈ wideHillStrip n) {k : ℤ} (hk : k.natAbs ≠ n) :
    |(n : ℝ)^2-(k : ℝ)^2| ≤ ‖z-(freeHillValue k : ℂ)‖ := by
  let d : ℝ := |(n : ℝ)^2-(k : ℝ)^2|
  have hgap : 2*(n : ℝ)-1 ≤ d := two_mul_nat_sub_one_le_abs_sq_sub_sq (by omega) hk
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have he : Real.pi^2*d = |freeHillValue n-freeHillValue k| := by
    dsimp [d, freeHillValue]
    simp only [Int.cast_natCast]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg Real.pi)]
  have ht : Real.pi^2*d ≤ 12*(n : ℝ)+‖z-(freeHillValue k : ℂ)‖ := by
    rw [he]
    calc
      _ ≤ |freeHillValue n-z.re|+|z.re-freeHillValue k| := by
        simpa using abs_add_le (freeHillValue n-z.re) (z.re-freeHillValue k)
      _ ≤ _ := add_le_add (by simpa only [wideHillStrip, mem_ofPred_eq, abs_sub_comm] using hz)
        (by simpa using Complex.abs_re_le_norm (z-(freeHillValue k : ℂ)))
  have hd : 0 ≤ d := abs_nonneg _
  nlinarith

/-- The supplementary wide strips cover the high real half-line.
This is a geometric covering statement, independent of the potential. -/
theorem exists_wideHillStrip_of_ge (N : ℕ) (hN : 2 ≤ N) (lambda : ℝ)
    (hlambda : freeHillValue N ≤ lambda) :
    ∃ n : ℕ, N ≤ n ∧ (lambda : ℂ) ∈ wideHillStrip n := by
  have hl0 : 0 ≤ lambda := (by unfold freeHillValue; positivity : 0 ≤ freeHillValue N).trans hlambda
  let t := Real.sqrt lambda/Real.pi
  let m := Nat.floor t
  have ht0 : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  have hNt : (N : ℝ) ≤ t := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    have hs : ((N : ℝ)*Real.pi)^2 ≤ (Real.sqrt lambda)^2 := by
      rw [Real.sq_sqrt hl0]
      simpa only [freeHillValue, Int.cast_natCast, mul_pow, mul_comm] using hlambda
    exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hs
  have hNm : N ≤ m := Nat.le_floor hNt
  have hlo : freeHillValue m ≤ lambda := by
    have h := (le_div_iff₀ Real.pi_pos).mp (Nat.floor_le ht0)
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ)*Real.pi)
      (Real.sqrt_nonneg lambda)).mpr h
    rw [Real.sq_sqrt hl0] at hs
    simpa only [freeHillValue, Int.cast_natCast, mul_pow, mul_comm] using hs
  have hhi : lambda < freeHillValue (m+1 : ℕ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp (Nat.lt_floor_add_one t)
    have hs := (sq_lt_sq₀ (Real.sqrt_nonneg lambda)
      (by positivity : 0 ≤ ((m : ℝ)+1)*Real.pi)).mpr h
    rw [Real.sq_sqrt hl0] at hs
    simpa only [freeHillValue, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one, mul_pow, mul_comm] using hs
  have hstep : freeHillValue (m+1 : ℕ)-freeHillValue m ≤
      12*(m : ℝ)+12*((m+1 : ℕ) : ℝ) := by
    have hpi : Real.pi^2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hp := mul_nonneg (sub_nonneg.mpr hpi) (by positivity : 0 ≤ 2*(m : ℝ)+1)
    dsimp [freeHillValue]
    push_cast
    nlinarith
  by_cases hm : lambda ≤ freeHillValue m+12*(m : ℝ)
  · refine ⟨m,hNm,?_⟩
    change |lambda-freeHillValue m| ≤ 12*(m : ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  · refine ⟨m+1,by omega,?_⟩
    change |lambda-freeHillValue (m+1 : ℕ)| ≤ 12*((m+1 : ℕ) : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hhi.le)]
    linarith

theorem exists_wideHillStrip_of_ge_lower_edge (N : ℕ) (hN : 2 ≤ N) (lambda : ℝ)
    (hlambda : freeHillValue N-12*(N : ℝ) ≤ lambda) :
    ∃ n : ℕ, N ≤ n ∧ (lambda : ℂ) ∈ wideHillStrip n := by
  by_cases h : freeHillValue N ≤ lambda
  · exact exists_wideHillStrip_of_ge N hN lambda h
  · refine ⟨N,le_rfl,?_⟩
    change |lambda-freeHillValue N| ≤ 12*(N : ℝ)
    rw [abs_of_nonpos (by linarith)]
    linarith


end NLS.KdV
