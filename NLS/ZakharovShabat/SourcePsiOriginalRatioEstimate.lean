import NLS.ZakharovShabat.SourcePsiOriginalCoordinateBound

/-!
# The reciprocal-distance error on every original isolating disk

The finite head and the free tail give a uniform displacement bound for
the entire disk family. Combined with original separation, this gives
the O(1/(n-m)) term in (2.26), with a filled unused root in its own disk.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.exists_uniform_lattice_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℤ, ∀ z ∈ D m, ‖z-(Real.pi:ℂ)*m‖ ≤ A := by
  classical
  obtain ⟨N,hN⟩ := hD.tail
  choose d r hr he using hD.discs
  let S := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let B : ℤ → ℝ := fun m => r m+‖(d m:ℂ)-(Real.pi:ℂ)*m‖
  have hB (m : ℤ) : 0 ≤ B m := add_nonneg (hr m).le (norm_nonneg _)
  refine ⟨Real.pi/4+∑ m ∈ S, B m,
    add_nonneg (by positivity) (Finset.sum_nonneg (fun m _ => hB m)),?_⟩
  intro m z hz
  by_cases hm : N < m.natAbs
  · rw [hN m hm] at hz
    have hb : ‖z-(Real.pi:ℂ)*m‖ < Real.pi/4 := by
      simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hz
    exact hb.le.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => hB m)))
  · have hmS : m ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hb : ‖z-(d m:ℂ)‖ < r m := by simpa only [he m,mem_ball,dist_eq_norm] using hz
    calc
      ‖z-(Real.pi:ℂ)*m‖ ≤ ‖z-(d m:ℂ)‖+‖(d m:ℂ)-(Real.pi:ℂ)*m‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B m := add_le_add hb.le le_rfl
      _ ≤ ∑ k ∈ S, B k := Finset.single_le_sum (fun k _ => hB k) hmS
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem sourcePsi_indexRatio_error_bound
    (n m : ℤ) (hmn : m ≠ n) (ξ z : ℂ) (hξz : ξ ≠ z)
    (A B c : ℝ) (hz : ‖z-(Real.pi:ℂ)*m‖ ≤ A) (hξ : ‖ξ-(Real.pi:ℂ)*n‖ ≤ B)
    (hsep : ‖((n-m:ℤ):ℂ)‖/‖ξ-z‖ ≤ c) :
    ‖((n-m:ℤ):ℂ)/(ξ-z)-(Real.pi:ℂ)⁻¹‖ ≤
      ((A+B)/Real.pi*c)/‖((n-m:ℤ):ℂ)‖ := by
  have hden : 0 < ‖ξ-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hξz)
  have hn : 0 < ‖((n-m:ℤ):ℂ)‖ := by
    apply norm_pos_iff.mpr
    exact_mod_cast sub_ne_zero.mpr hmn.symm
  have hAB : 0 ≤ A+B := add_nonneg ((norm_nonneg _).trans hz) ((norm_nonneg _).trans hξ)
  have hinv : 1/‖ξ-z‖ ≤ c/‖((n-m:ℤ):ℂ)‖ := by
    apply (div_le_div_iff₀ hden hn).mpr
    simpa only [one_mul] using (div_le_iff₀ hden).mp hsep
  have he : ((n-m:ℤ):ℂ)/(ξ-z)-(Real.pi:ℂ)⁻¹ =
      (z-(Real.pi:ℂ)*m-(ξ-(Real.pi:ℂ)*n))/((Real.pi:ℂ)*(ξ-z)) := by
    push_cast
    field_simp [sub_ne_zero.mpr hξz,show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]
    ring
  rw [he,norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ (A+B)/(Real.pi*‖ξ-z‖) := div_le_div_of_nonneg_right
      ((norm_sub_le _ _).trans (add_le_add hz hξ)) (by positivity)
    _ = ((A+B)/Real.pi)*(1/‖ξ-z‖) := by ring
    _ ≤ ((A+B)/Real.pi)*(c/‖((n-m:ℤ):ℂ)‖) :=
      mul_le_mul_of_nonneg_left hinv (div_nonneg hAB Real.pi_pos.le)
    _ = _ := by ring

end NLS.ZakharovShabat
