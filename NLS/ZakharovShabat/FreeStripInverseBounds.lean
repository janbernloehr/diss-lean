import NLS.ZakharovShabat.FreeResolventExteriorLimit
import NLS.ZakharovShabat.PerturbedSpectralProducts

/-!
# Inverse free factors on horizontal strips

Periodicity reduces the real coordinate to a compact rectangle. Fixed
separation from the free lattice then bounds the inverses of both parity
factors, uniformly along the whole strip.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- Either free parity factor is nonzero away from the full free lattice. -/
theorem freeDiscriminant_sub_ne_zero_of_sq_eq_four (b : ℂ) (hb : b^2 = 4)
    (z : ℂ) (hz : z ∉ freeLattice) : freeDiscriminant z-b ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  exact freeDiscriminant_sq_sub_four_ne_zero z hz (by rw [he, hb, sub_self])

/-- Subtracting an even free lattice point preserves the free trace. -/
theorem freeDiscriminant_sub_even_center (z : ℂ) (n : ℤ) :
    freeDiscriminant (z-(Real.pi : ℂ)*(2*n)) = freeDiscriminant z := by
  have he : (Real.pi : ℂ)*(2*n) = (n : ℂ)*(2*Real.pi) := by ring
  simp only [freeDiscriminant, he, Complex.cos_sub_int_mul_two_pi]

/-- Separation from every free center is invariant under even lattice translation. -/
theorem separated_sub_even_center {r : ℝ} {z : ℂ}
    (hz : ∀ m : ℤ, r ≤ ‖z-(Real.pi : ℂ)*m‖) (n m : ℤ) :
    r ≤ ‖(z-(Real.pi : ℂ)*(2*n))-(Real.pi : ℂ)*m‖ := by
  have he : (z-(Real.pi : ℂ)*(2*n))-(Real.pi : ℂ)*m =
      z-(Real.pi : ℂ)*(2*n+m : ℤ) := by push_cast; ring
  rw [he]
  exact hz (2*n+m)

/-- Both free parity inverses are bounded on every strip outside fixed free discs. -/
theorem exists_bound_freeDiscriminant_sub_inv_strip (b : ℂ) (hb : b^2 = 4)
    {r : ℝ} (hr : 0 < r) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ H →
      (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) → ‖(freeDiscriminant z-b)⁻¹‖ ≤ C := by
  let S : Set ℂ := {z | ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_le continuous_const (by fun_prop))
  let K := closedBall (0 : ℂ) (Real.pi+H) ∩ S
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right hS
  have hc : ContinuousOn (fun z : ℂ => (freeDiscriminant z-b)⁻¹) K := by
    apply ContinuousOn.inv₀
    · exact (show Continuous (fun z : ℂ => freeDiscriminant z-b) by
        unfold freeDiscriminant; fun_prop).continuousOn
    · intro z hz
      exact freeDiscriminant_sub_ne_zero_of_sq_eq_four b hb z
        (notMem_freeLattice_of_separated hr hz.2)
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz hsep
  obtain ⟨n, hn⟩ := exists_centered_real_part (z/2)
  let w := z-(Real.pi : ℂ)*(2*n)
  have hwr : |w.re| ≤ Real.pi := by
    have he : w.re = 2*((z/2).re-Real.pi*n) := by
      simp [w]; ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hwi : w.im = z.im := by simp [w]
  have hw : w ∈ K := by
    refine ⟨?_, separated_sub_even_center hsep n⟩
    simp only [mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im w).trans (by rw [hwi]; linarith)
  have he : freeDiscriminant w = freeDiscriminant z := freeDiscriminant_sub_even_center z n
  have hbound := hC _ ⟨w, hw, rfl⟩
  dsimp only at hbound
  rw [he] at hbound
  exact hbound.trans (le_max_left _ _)

end NLS.ZakharovShabat
