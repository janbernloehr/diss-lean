import NLS.Fourier.IntervalSobolevNormEquivalence
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The fractional difference quotient as an actual `L²` function

The intrinsic fractional energy is the square integral of the physical
quotient `(f(x)-f(y))/|x-y|^(1/2+s)` on the interval product. Almost-everywhere
invariance and linearity allow this quotient to define a Hilbert graph norm.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Product Lebesgue measure on the open interval square. -/
def intervalProductMeasure (L : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo 0 L)).prod (volume.restrict (Ioo 0 L))

/-- The physical fractional difference quotient, with the real-power convention on the diagonal. -/
def fractionalDifferenceQuotient (s : ℝ) (f : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (|p.1 - p.2| ^ (-(1 / 2 + s)) : ℝ) * (f p.1 - f p.2)

@[fun_prop] theorem measurable_fractionalDifferenceQuotient (s : ℝ) {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (fractionalDifferenceQuotient s f) := by
  unfold fractionalDifferenceQuotient
  fun_prop

/-- Squaring the quotient gives exactly the kernel integrand, including diagonal points. -/
theorem ofReal_norm_sq_fractionalDifferenceQuotient (s : ℝ) (f : ℝ → ℂ) (p : ℝ × ℝ) :
    ENNReal.ofReal (‖fractionalDifferenceQuotient s f p‖ ^ 2) =
      ENNReal.ofReal (‖f p.1 - f p.2‖ ^ 2) * fractionalDistanceKernel s p.1 p.2 := by
  simp only [fractionalDifferenceQuotient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), mul_pow]
  rw [← Real.rpow_two (|p.1 - p.2| ^ (-(1 / 2 + s))), ← Real.rpow_mul (abs_nonneg _),
    show (-(1 / 2 + s)) * 2 = -(1 + 2 * s) by ring,
    ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
  exact mul_comm _ _

/-- The quotient depends only on the interval almost-everywhere class. -/
theorem fractionalDifferenceQuotient_congr {L s : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) :
    fractionalDifferenceQuotient s f =ᵐ[intervalProductMeasure L] fractionalDifferenceQuotient s g := by
  have hx := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioo 0 L)) (ν := volume.restrict (Ioo 0 L))).ae_eq h
  have hy := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioo 0 L)) (ν := volume.restrict (Ioo 0 L))).ae_eq h
  filter_upwards [hx, hy] with p hp hq
  dsimp only [Function.comp_def] at hp hq
  simp only [fractionalDifferenceQuotient, hp, hq]

@[simp] theorem fractionalDifferenceQuotient_zero (s : ℝ) : fractionalDifferenceQuotient s 0 = 0 := by
  funext p
  simp [fractionalDifferenceQuotient]

theorem fractionalDifferenceQuotient_add (s : ℝ) (f g : ℝ → ℂ) :
    fractionalDifferenceQuotient s (f + g) = fractionalDifferenceQuotient s f + fractionalDifferenceQuotient s g := by
  funext p
  simp only [fractionalDifferenceQuotient, Pi.add_apply]
  ring

theorem fractionalDifferenceQuotient_smul (s : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    fractionalDifferenceQuotient s (c • f) = c • fractionalDifferenceQuotient s f := by
  funext p
  simp only [fractionalDifferenceQuotient, Pi.smul_apply, smul_eq_mul]
  ring

/-- Tonelli identifies the intrinsic energy with the actual quotient's product-space square integral. -/
theorem fractionalIntervalEnergy_eq_quotient_integral (s L : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    fractionalIntervalEnergy s L f =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (‖fractionalDifferenceQuotient s f p‖ ^ 2) ∂intervalProductMeasure L := by
  have hm : Measurable (fun p => ENNReal.ofReal (‖fractionalDifferenceQuotient s f p‖ ^ 2)) := by fun_prop
  rw [intervalProductMeasure, lintegral_prod _ hm.aemeasurable]
  simp only [ofReal_norm_sq_fractionalDifferenceQuotient, fractionalIntervalEnergy]

/-- Finite intrinsic energy is exactly square integrability of the difference quotient. -/
theorem memLp_fractionalDifferenceQuotient_iff (s L : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    MemLp (fractionalDifferenceQuotient s f) 2 (intervalProductMeasure L) ↔ fractionalIntervalEnergy s L f < ⊤ := by
  have hq := measurable_fractionalDifferenceQuotient s hf
  have hN : Measurable (fun p => ‖fractionalDifferenceQuotient s f p‖ ^ 2) := by fun_prop
  rw [memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable, fractionalIntervalEnergy_eq_quotient_integral s L f hf]
  constructor
  · intro h
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp h.2
  · intro h
    exact ⟨hN.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mpr h⟩

/-- The square norm of a complex `L²` class is its actual physical square integral. -/
theorem norm_sq_L2_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    _ = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ x, inner ℝ (f x) (f x) ∂μ := L2.inner_def _ _
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

theorem ofReal_norm_sq_L2_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [norm_sq_L2_eq_integral]
  exact ofReal_integral_eq_lintegral_ofReal ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

/-- The quotient's `L²` class has exactly the intrinsic fractional energy as its squared norm. -/
theorem ofReal_norm_sq_fractionalDifferenceQuotient_toLp (s L : ℝ) (f : ℝ → ℂ) (hf : Measurable f)
    (h : MemLp (fractionalDifferenceQuotient s f) 2 (intervalProductMeasure L)) :
    ENNReal.ofReal (‖h.toLp (fractionalDifferenceQuotient s f)‖ ^ 2) = fractionalIntervalEnergy s L f := by
  rw [ofReal_norm_sq_L2_eq_lintegral, fractionalIntervalEnergy_eq_quotient_integral s L f hf]
  apply lintegral_congr_ae
  filter_upwards [h.coeFn_toLp] with p hp
  rw [hp]

end NLS.Fourier
