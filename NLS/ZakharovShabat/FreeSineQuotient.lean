import NLS.ZakharovShabat.FreeSineExteriorBounds
import Mathlib.Analysis.Calculus.DSlope

/-!
# The filled sine quotient at each free spectral center

The divided difference fills sin(z)/(z-pi*n) at the center by its derivative.
Translation and compactness give one bound on every disc of a fixed radius,
independent of the signed lattice index.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- The sine quotient with its removable singularity filled. -/
def freeSineQuotient (n : ℤ) (z : ℂ) : ℂ :=
  cos ((Real.pi : ℂ)*n)*dslope sin 0 (z-(Real.pi : ℂ)*n)

/-- The translating cosine has unit norm, also at negative lattice indices. -/
theorem norm_cos_freeCenter (n : ℤ) : ‖cos ((Real.pi : ℂ)*n)‖ = 1 := by
  have he : (Real.pi : ℂ)*n = ((n*Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← ofReal_cos, norm_real, Real.norm_eq_abs, Real.abs_cos_int_mul_pi]

/-- Filling the quotient preserves the exact sine factorization, including at the center. -/
theorem freeSineQuotient_mul_sub (n : ℤ) (z : ℂ) :
    freeSineQuotient n z*(z-(Real.pi : ℂ)*n) = sin z := by
  have hs : (z-(Real.pi : ℂ)*n)*dslope sin 0 (z-(Real.pi : ℂ)*n) =
      sin (z-(Real.pi : ℂ)*n) := by
    simpa only [sub_zero, smul_eq_mul, sin_zero] using sub_smul_dslope sin 0 (z-(Real.pi : ℂ)*n)
  have hsin : sin ((Real.pi : ℂ)*n) = 0 := by simpa [mul_comm] using sin_int_mul_pi n
  calc
    _ = cos ((Real.pi : ℂ)*n)*sin (z-(Real.pi : ℂ)*n) := by rw [freeSineQuotient]; calc
      _ = cos ((Real.pi : ℂ)*n)*((z-(Real.pi : ℂ)*n)*dslope sin 0 (z-(Real.pi : ℂ)*n)) := by ring
      _ = _ := by rw [hs]
    _ = sin ((z-(Real.pi : ℂ)*n)+(Real.pi : ℂ)*n) := by rw [sin_add, hsin]; ring
    _ = _ := by ring_nf

/-- Away from the center the filled function is the usual quotient. -/
theorem freeSineQuotient_eq_div (n : ℤ) (z : ℂ) (hz : z ≠ (Real.pi : ℂ)*n) :
    freeSineQuotient n z = sin z/(z-(Real.pi : ℂ)*n) :=
  (eq_div_iff (sub_ne_zero.mpr hz)).mpr (freeSineQuotient_mul_sub n z)

/-- The removable value is the free derivative, with its correct sign. -/
theorem freeSineQuotient_center (n : ℤ) :
    freeSineQuotient n ((Real.pi : ℂ)*n) = cos ((Real.pi : ℂ)*n) := by
  simp [freeSineQuotient, Complex.deriv_sin]

/-- The quotient is continuous even at the free center. -/
theorem continuous_freeSineQuotient (n : ℤ) : Continuous (freeSineQuotient n) := by
  have h : Continuous (dslope sin 0) := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst z
      exact continuousAt_dslope_same.mpr (Complex.differentiable_sin 0)
    · exact (continuousAt_dslope_of_ne hz).mpr (Complex.continuous_sin.continuousAt)
  exact continuous_const.mul (h.comp (continuous_id.sub continuous_const))

/-- One finite constant bounds every filled sine quotient on every fixed-radius free disc. -/
theorem exists_bound_freeSineQuotient (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ r → ‖freeSineQuotient n z‖ ≤ C := by
  have hc : Continuous (dslope sin 0) := by
    have h : Continuous (fun z => freeSineQuotient 0 z) := continuous_freeSineQuotient 0
    simpa [freeSineQuotient] using h
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun n z hz => ?_⟩
  rw [freeSineQuotient, norm_mul, norm_cos_freeCenter, one_mul]
  exact (hC _ (by simpa only [mem_closedBall, dist_zero_right] using hz)).trans (le_max_left _ _)

end NLS.ZakharovShabat
