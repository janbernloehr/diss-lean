import NLS.ZakharovShabat.FreeDiscProductMajorant
import NLS.ZakharovShabat.FreeSineQuotient
import NLS.ZakharovShabat.LocalSpectralFactors

/-!
# Restoring the local sine-product factor

The filled local formula agrees with sin(z) times the full relative product
away from the free lattice. Its error from sin(z) has a common lp majorant
throughout every closed half-pi free disc, uniformly on displacement norm
balls. No nonvanishing assumption on the spectral numerators is needed.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The local sine product, including its removable value at the free center. -/
def restoredSineProduct (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  freeSineQuotient n z*(z-(Real.pi : ℂ)*n-a n)*freeDiscRelativeProduct a n z

/-- Restoring the local factor gives exactly the full relative sine product off the lattice. -/
theorem restoredSineProduct_eq_offLattice (hp : p ≠ ⊤) (a : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∉ freeLattice) :
    restoredSineProduct a n z = Complex.sin z*
      ∏' k : ℤ, ((Real.pi : ℂ)*k+a k-z)/((Real.pi : ℂ)*k-z) := by
  let ξ : ℤ → ℂ := fun k => (Real.pi : ℂ)*k+a k
  have hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p := by
    simpa [ξ] using (show Memℓp (fun k => a k) p from lp.memℓp a)
  have he := spectralRelativeProduct_eq_local_mul hp ξ hξ z hz n
  simp only [spectralRelativeFactor, ξ] at he
  rw [he]
  change freeSineQuotient n z*(z-(Real.pi : ℂ)*n-a n)*freeDiscRelativeProduct a n z =
    Complex.sin z*(((Real.pi : ℂ)*n+a n-z)/((Real.pi : ℂ)*n-z)*freeDiscRelativeProduct a n z)
  rw [freeSineQuotient_eq_div n z (sub_ne_zero.mp (free_denominator_ne_zero hz n))]
  rw [show (Real.pi : ℂ)*n-z = -(z-(Real.pi : ℂ)*n) by ring, div_neg]
  ring

omit [Fact (1 ≤ p)] in
/-- The center value retains the local displacement and the omitted-diagonal product. -/
theorem restoredSineProduct_center (a : Coeff p) (n : ℤ) :
    restoredSineProduct a n ((Real.pi : ℂ)*n) =
      -Complex.cos ((Real.pi : ℂ)*n)*a n*freeDiscRelativeProduct a n ((Real.pi : ℂ)*n) := by
  rw [restoredSineProduct, freeSineQuotient_center]
  ring

/-- A positive lp sequence controlling the restored product error. -/
def restoredSineProductMajorant (hp1 : 1 < p) (hp : p ≠ ⊤) (C : ℝ) (a : Coeff p) : Coeff p :=
  (C : ℂ) • (((Real.pi/2+‖a‖ : ℝ) : ℂ) • Coeff.magnitude (freeDiscProductMajorant hp1 hp a)+Coeff.magnitude a)

/-- The restored majorant has an exact positive coefficient formula. -/
theorem norm_restoredSineProductMajorant_apply (hp1 : 1 < p) (hp : p ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C) (a : Coeff p) (n : ℤ) :
    ‖restoredSineProductMajorant hp1 hp C a n‖ =
      C*((Real.pi/2+‖a‖)*‖freeDiscProductMajorant hp1 hp a n‖+‖a n‖) := by
  simp only [restoredSineProductMajorant, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_add,
    Pi.add_apply, smul_eq_mul, Coeff.magnitude_apply,
    ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg (by positivity)]

/-- The restored product error is controlled everywhere in the closed free disc. -/
theorem norm_restoredSineProduct_sub_sin_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖restoredSineProduct a n z-Complex.sin z‖ ≤ ‖restoredSineProductMajorant hp1 hp C a n‖ := by
  rw [norm_restoredSineProductMajorant_apply hp1 hp hC]
  have he : restoredSineProduct a n z-Complex.sin z = freeSineQuotient n z*
      ((z-(Real.pi : ℂ)*n-a n)*(freeDiscRelativeProduct a n z-1)-a n) := by
    rw [← freeSineQuotient_mul_sub n z, restoredSineProduct]
    ring
  have ha := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' a n
  have hw : ‖z-(Real.pi : ℂ)*n-a n‖ ≤ Real.pi/2+‖a‖ :=
    (norm_sub_le _ _).trans (add_le_add hz ha)
  rw [he, norm_mul]
  apply mul_le_mul (hbound n z hz) _ (norm_nonneg _) hC
  exact (norm_sub_le _ _).trans (by
    rw [norm_mul]
    exact add_le_add (mul_le_mul hw (norm_freeDiscRelativeProduct_sub_one_le hp1 hp a n z hz)
      (norm_nonneg _) (by positivity)) le_rfl)

/-- The restored majorant has a bound in terms of displacement and relative-product norms. -/
theorem norm_restoredSineProductMajorant_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C) (a : Coeff p) :
    ‖restoredSineProductMajorant hp1 hp C a‖ ≤
      C*((Real.pi/2+‖a‖)*‖freeDiscProductMajorant hp1 hp a‖+‖a‖) := by
  rw [restoredSineProductMajorant, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
  apply mul_le_mul_of_nonneg_left _ hC
  apply (norm_add_le _ _).trans
  rw [norm_smul, Coeff.norm_magnitude, Coeff.norm_magnitude]
  have hc : ‖((Real.pi/2+‖a‖ : ℝ) : ℂ)‖ = Real.pi/2+‖a‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hc]

/-- Arbitrary simultaneous samples, including centers and boundaries, give an lp sine error. -/
theorem memℓp_restoredSineProduct_sub_sin (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    Memℓp (fun n => restoredSineProduct a n (z n)-Complex.sin (z n)) p := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  exact (lp.memℓp (restoredSineProductMajorant hp1 hp C a)).mono'
    (fun n => norm_restoredSineProduct_sub_sin_le hp1 hp hC hbound a n (z n) (hz n))

/-- One norm bound works for majorants on an entire displacement norm ball. -/
theorem exists_uniform_restoredSineProduct_majorants (hp1 : 1 < p) (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) : ∃ K : ℝ, 0 ≤ K ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∃ A : Coeff p, ‖A‖ ≤ K ∧ ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
        ‖restoredSineProduct a n z-Complex.sin z‖ ≤ ‖A n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  let B := (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*(R/Real.pi)+
    Real.exp (absoluteSampledRowConstant hp*(R/Real.pi))*(absoluteSampledRowConstant hp*(R/Real.pi))^2
  have hB : 0 ≤ B := by
    have := hilbertTransformBound_nonneg hp1 hp
    dsimp [B]
    positivity
  refine ⟨C*((Real.pi/2+R)*B+R), by positivity, fun a ha =>
    ⟨restoredSineProductMajorant hp1 hp C a, ?_, fun n z hz =>
      norm_restoredSineProduct_sub_sin_le hp1 hp hC hbound a n z hz⟩⟩
  apply (norm_restoredSineProductMajorant_le hp1 hp hC a).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add (mul_le_mul (add_le_add le_rfl ha)
    (norm_freeDiscProductMajorant_le hp1 hp a ha) (norm_nonneg _) (by positivity)) ha

/-- Off-lattice samples give the same lp estimate for the literal full relative sine product. -/
theorem memℓp_sin_relativeProduct_sub_sin (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2)
    (hfree : ∀ n, z n ∉ freeLattice) :
    Memℓp (fun n => Complex.sin (z n)*(∏' k : ℤ,
      ((Real.pi : ℂ)*k+a k-z n)/((Real.pi : ℂ)*k-z n))-Complex.sin (z n)) p := by
  have h := memℓp_restoredSineProduct_sub_sin hp1 hp a z hz
  simpa only [restoredSineProduct_eq_offLattice hp a _ _ (hfree _)] using h

end NLS.ZakharovShabat
