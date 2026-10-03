import NLS.ZakharovShabat.ClassicalTriangularPotential
import NLS.ZakharovShabat.ClassicalEndpointGradientEndpointObstruction
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Counterexample to the infinite outer endpoint of Appendix G.5

The physical H¹ potential `(1,0)` and frequencies
`νₙ = nπ + i/(2(|n|+1))` satisfy both printed frequency conditions.
At every index, the diagonal gradient error has a component outside
Fourier ℓ¹, for either free reference. Thus discarding finite heads
cannot repair the asserted `p=∞`, `p′=1` endpoint.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- A nonreal perturbation of the free lattice, including a harmless nonzero central term. -/
def gradientCounterexampleFrequency (n : ℤ) : ℂ :=
  (Real.pi : ℂ)*(n : ℂ)+I*((1/(2*((n.natAbs : ℝ)+1)) : ℝ) : ℂ)

@[simp] theorem gradientCounterexampleFrequency_im (n : ℤ) :
    (gradientCounterexampleFrequency n).im = 1/(2*((n.natAbs : ℝ)+1)) := by
  simp only [gradientCounterexampleFrequency,add_im,mul_im,ofReal_re,ofReal_im,
    intCast_re,intCast_im,I_re,I_im,mul_zero,zero_mul,zero_add,add_zero,one_mul]

theorem gradientCounterexampleFrequency_im_pos (n : ℤ) :
    0 < (gradientCounterexampleFrequency n).im := by
  rw [gradientCounterexampleFrequency_im]
  positivity

/-- Exact displacement from the lattice. -/
theorem norm_gradientCounterexampleFrequency_sub (n : ℤ) :
    ‖gradientCounterexampleFrequency n-(Real.pi : ℂ)*(n : ℂ)‖ =
      1/(2*((n.natAbs : ℝ)+1)) := by
  rw [gradientCounterexampleFrequency,add_sub_cancel_left,norm_mul,norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]

/-- The dissertation's radius π/4 condition holds at every index. -/
theorem gradientCounterexampleFrequency_close (n : ℤ) :
    ‖gradientCounterexampleFrequency n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ Real.pi/4 := by
  rw [norm_gradientCounterexampleFrequency_sub]
  have h : 1/(2*((n.natAbs : ℝ)+1)) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n.natAbs]
  exact h.trans (by linarith [Real.pi_gt_three])

/-- The stronger O(1/|n|) displacement condition also holds. -/
theorem gradientCounterexampleFrequency_decay (n : ℤ) (hn : n ≠ 0) :
    ‖gradientCounterexampleFrequency n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ (1/2 : ℝ)/(n.natAbs : ℝ) := by
  rw [norm_gradientCounterexampleFrequency_sub]
  have hn' : 0 < (n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn
  rw [div_le_div_iff₀ (by positivity) hn']
  nlinarith

/-- Actual H¹ data violate absolute Fourier summability at every nonreal frequency.
The free reference can be arbitrary because this diagonal free gradient is zero. -/
theorem not_memlp_triangular_gradient_one (z w : ℂ) (hz : z.im ≠ 0) :
    ¬Memℓp (intervalFourierCoefficient 1 (fun t =>
      (classicalEndpointGradientRemainder (classicalSobolevPotential triangularSobolevCoefficients)
        z w (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) t).2)) 1 := by
  rw [classicalSobolevPotential_triangular]
  exact not_memlp_classicalEndpointGradientRemainder_one_of_upper_ne_zero _ z w
    (classicalTriangularMonodromy_upper_ne_zero z hz)

/-- Failure at every index for every reference sequence, covering both assertions of G.5. -/
theorem not_memlp_gradientCounterexampleFrequency_one (ω : ℤ → ℂ) (n : ℤ) :
    ¬Memℓp (intervalFourierCoefficient 1 (fun t =>
      (classicalEndpointGradientRemainder (classicalSobolevPotential triangularSobolevCoefficients)
        (gradientCounterexampleFrequency n) (ω n) (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) t).2)) 1 :=
  not_memlp_triangular_gradient_one _ _ (ne_of_gt (gradientCounterexampleFrequency_im_pos n))

/-- No finite exceptional set can remove the obstruction. -/
theorem not_eventually_memlp_gradientCounterexampleFrequency_one (ω : ℤ → ℂ) :
    ¬∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
      Memℓp (intervalFourierCoefficient 1 (fun t =>
        (classicalEndpointGradientRemainder (classicalSobolevPotential triangularSobolevCoefficients)
          (gradientCounterexampleFrequency n) (ω n) (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) t).2)) 1 := by
  rintro ⟨N,hN⟩
  exact not_memlp_gradientCounterexampleFrequency_one ω (N : ℤ) (hN N (by simp))

end NLS.ZakharovShabat
