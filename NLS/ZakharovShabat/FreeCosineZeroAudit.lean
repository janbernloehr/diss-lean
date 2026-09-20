import NLS.ZakharovShabat.FreeResolventExteriorLimit
import NLS.ZakharovShabat.FreeSpectralProducts

/-!
# Audit of the printed cosine quotient in Lemma 8.1(iii)

The free discs have radius pi/4 about pi times the integers. Their complement
contains arbitrarily large zeros of the free cosine discriminant. The ordinary
quotient in the printed uniform bound is therefore undefined there; with Lean's
totalized division, its distance from one is exactly one for any numerator.
This audits that literal quotient, not an additive asymptotic or a quotient
restricted to a domain where cosine is bounded away from zero.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- Positive real free cosine zeros, halfway between consecutive free eigenvalues. -/
def freeCosineZero (n : ℕ) : ℂ := (Real.pi : ℂ)*((n : ℂ)+1/2)

@[simp] theorem freeCosineZero_im (n : ℕ) : (freeCosineZero n).im = 0 := by
  simp [freeCosineZero]

/-- Every such midpoint is on the edge of its centered vertical strip. -/
theorem freeCosineZero_mem_verticalStrip (n : ℕ) :
    freeCosineZero n ∈ verticalStrip (n : ℤ) (Real.pi/4) := by
  have he : freeCosineZero n-(Real.pi : ℂ)*(n : ℤ) = ((Real.pi/2 : ℝ) : ℂ) := by
    simp only [freeCosineZero, Int.cast_natCast]
    push_cast
    ring
  constructor
  · have h : (freeCosineZero n).re-Real.pi*(n : ℤ) = Real.pi/2 := by
      have h := congrArg Complex.re he
      simpa using h
    rw [h, abs_of_nonneg (by positivity)]
  · rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [Real.pi_pos]

/-- Free cosine zeros lie outside every open free spectral disc. -/
theorem freeCosineZero_separated (n : ℕ) (k : ℤ) :
    Real.pi/4 ≤ ‖freeCosineZero n-(Real.pi : ℂ)*k‖ := by
  have h := verticalStrip_denominator_lower (m := k)
    (by positivity : 0 < Real.pi/4) le_rfl (freeCosineZero_mem_verticalStrip n)
  have ha := mul_nonneg (by positivity : 0 ≤ Real.pi/4)
    (abs_nonneg (((k-(n : ℤ) : ℤ) : ℝ)))
  nlinarith

/-- The audit points escape to arbitrarily large spectral norm. -/
theorem tendsto_norm_freeCosineZero : Tendsto (fun n => ‖freeCosineZero n‖) atTop atTop := by
  have hn (n : ℕ) : ‖freeCosineZero n‖ = Real.pi*((n : ℝ)+1/2) := by
    have he : freeCosineZero n = ((Real.pi*((n : ℝ)+1/2) : ℝ) : ℂ) := by
      simp only [freeCosineZero]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : Tendsto (fun n : ℕ => (n : ℝ)+1/2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa only [hn] using hs.const_mul_atTop Real.pi_pos

@[simp] theorem freeDiscriminant_freeCosineZero (n : ℕ) : freeDiscriminant (freeCosineZero n) = 0 := by
  have he : freeCosineZero n = (n : ℂ)*Real.pi+Real.pi/2 := by unfold freeCosineZero; ring
  simp only [freeDiscriminant, he, Complex.cos_add_pi_div_two, Complex.sin_nat_mul_pi,
    neg_zero, mul_zero]

/-- At the included denominator zeros, Lean's totalized quotient has error exactly one. -/
theorem norm_div_free_at_freeCosineZero (f : ℂ → ℂ) (n : ℕ) :
    ‖f (freeCosineZero n)/freeDiscriminant (freeCosineZero n)-1‖ = 1 := by
  simp

/-- No numerator can satisfy the literal totalized quotient bound on the printed exterior set. -/
theorem not_exists_exterior_cosine_quotient_bound (f : ℂ → ℂ) :
    ¬ ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ k : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*k‖) →
      ‖f z/freeDiscriminant z-1‖ ≤ (1 : ℝ)/2 := by
  rintro ⟨R, hR⟩
  obtain ⟨n, hn⟩ := (tendsto_norm_freeCosineZero.eventually_ge_atTop R).exists
  have h := hR (freeCosineZero n) hn (freeCosineZero_separated n)
  rw [norm_div_free_at_freeCosineZero] at h
  norm_num at h

end NLS.ZakharovShabat
