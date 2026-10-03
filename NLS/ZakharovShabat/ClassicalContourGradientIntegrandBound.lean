import NLS.ZakharovShabat.ClassicalSobolevContourQuotient
import NLS.ZakharovShabat.ClassicalDiscriminantGradientDiscSup

/-! # Summable Fourier bounds for the actual G.7 contour integrand

The spectral quotient multiplies the actual physical discriminant
gradient. One majorant controls all points on all sufficiently distant
contours and the entire H¹ potential ball, with no denominator hypothesis.
-/

noncomputable section
open Set Metric NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual Fourier coefficients of Δ/(Δ²−4) times a scalar gradient observation. -/
def classicalDiscriminantQuotientGradientFourierCoefficients {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  (classicalDiscriminant φ z/((classicalDiscriminant φ z)^2-4)) •
    classicalDiscriminantGradientFourierCoefficients hq φ z P

@[simp] theorem classicalDiscriminantQuotientGradientFourierCoefficients_apply
    {q : ℝ≥0∞} (hq : 1 < q) (φ : Curve (ℂ × ℂ)) (z : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalDiscriminantQuotientGradientFourierCoefficients hq φ z P k =
      intervalFourierCoefficient 1 (fun t =>
        classicalDiscriminant φ z/((classicalDiscriminant φ z)^2-4)*
          P (classicalDiscriminantGradient φ z t)) k := by
  simp only [classicalDiscriminantQuotientGradientFourierCoefficients,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,classicalDiscriminantGradientFourierCoefficients_apply,intervalFourierCoefficient_const_mul]

/-- The full integrand has a common summable majorant and no poles on every distant contour. -/
theorem exists_classicalContourGradientIntegrand_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 < r) (hrπ : r ≤ Real.pi/2) :
    ∃ N : ℕ, 0 < N ∧ ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ, N ≤ n.natAbs →
      ∀ z : ℂ, z ∈ sphere ((Real.pi : ℂ)*(n : ℂ)) r →
      (classicalDiscriminant (classicalSobolevPotential a) z)^2-4 ≠ 0 ∧
      ‖classicalDiscriminantQuotientGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) z P‖ ≤ b n := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨N,hN,δ,Q,hδ,hQ,hquot⟩ := exists_classicalSobolev_contour_discriminant_quotient_bound M hM r hr hrπ
  obtain ⟨b,hb,hgrad⟩ := exists_classicalDiscriminantGradient_disc_uniform_memlp p hp q hq M hM r hr.le
  refine ⟨N,hN,fun n => Q*b n,hb.const_mul Q,?_⟩
  intro a ha P hP n hn z hz
  obtain ⟨hden,hval⟩ := hquot a ha n hn z hz
  refine ⟨norm_pos_iff.mp (hδ.trans_le hden),?_⟩
  have hz' : ‖z-(Real.pi : ℂ)*(n : ℂ)‖ ≤ r := by
    exact le_of_eq (by simpa only [mem_sphere,dist_eq_norm] using hz)
  rw [classicalDiscriminantQuotientGradientFourierCoefficients,norm_smul]
  exact mul_le_mul hval (hgrad a ha P hP n z hz') (norm_nonneg _) hQ

end NLS.ZakharovShabat
