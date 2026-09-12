import NLS.Fourier.FractionalHardy

/-!
# Zero extension of fractional interval data

The full real-line difference energy splits into the intrinsic interval energy
and twice the interaction with the exterior. Fractional Hardy control therefore
proves zero-extension regularity below half, with no endpoint matching condition.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Extend interval values by zero; endpoint choices are immaterial in `L²`. -/
def intervalZeroExtension (L : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Ioo 0 L).indicator f

@[simp] theorem intervalZeroExtension_of_mem {L x : ℝ} (f : ℝ → ℂ) (hx : x ∈ Ioo 0 L) :
    intervalZeroExtension L f x = f x := indicator_of_mem hx f

@[simp] theorem intervalZeroExtension_of_notMem {L x : ℝ} (f : ℝ → ℂ) (hx : x ∉ Ioo 0 L) :
    intervalZeroExtension L f x = 0 := indicator_of_notMem hx f

/-- Full real-line fractional difference energy as a nonnegative double integral. -/
def fractionalLineEnergy (s : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalDistanceKernel s x y

theorem measurable_fractionalDistanceKernel (s : ℝ) :
    Measurable (fun p : ℝ × ℝ => fractionalDistanceKernel s p.1 p.2) := by
  unfold fractionalDistanceKernel
  fun_prop

theorem fractionalLineEnergy_congr {s : ℝ} {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    fractionalLineEnergy s f = fractionalLineEnergy s g := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  rw [hx, hy]

theorem intervalZeroExtension_congr {L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) :
    intervalZeroExtension L f =ᵐ[volume] intervalZeroExtension L g :=
  (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioo).mp h

/-- Zero extension preserves exactly the square-integrability condition. -/
theorem memLp_intervalZeroExtension_iff (L : ℝ) (f : ℝ → ℂ) :
    MemLp (intervalZeroExtension L f) 2 volume ↔ MemLp f 2 (volume.restrict (Ioo 0 L)) :=
  memLp_indicator_iff_restrict measurableSet_Ioo

/-- The global square energy of the zero extension is the interval square energy. -/
theorem squareEnergy_intervalZeroExtension (L : ℝ) (f : ℝ → ℂ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (‖intervalZeroExtension L f x‖ ^ 2)) =
      ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2) := by
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Ioo 0 L
  · simp only [intervalZeroExtension_of_mem f hx, indicator_of_mem hx]
  · simp [intervalZeroExtension_of_notMem f hx, indicator_of_notMem hx]

/-- Exact decomposition for measurable interval data, retaining infinite energies. -/
theorem fractionalLineEnergy_zeroExtension_of_measurable (s L : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    fractionalLineEnergy s (intervalZeroExtension L f) =
      fractionalIntervalEnergy s L f + 2 * fractionalExteriorEnergy s L f := by
  let A := Ioo (0 : ℝ) L
  let μ := volume.restrict A
  let ν := volume.restrict Aᶜ
  let g := intervalZeroExtension L f
  let F := fun p : ℝ × ℝ => ENNReal.ofReal (‖g p.1 - g p.2‖ ^ 2) * fractionalDistanceKernel s p.1 p.2
  have hg : Measurable g := hf.indicator measurableSet_Ioo
  have hm : Measurable F := (show Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (‖g p.1 - g p.2‖ ^ 2)) by
    fun_prop).mul (measurable_fractionalDistanceKernel s)
  have hsym (x y : ℝ) : F (x, y) = F (y, x) := by
    simp only [F, fractionalDistanceKernel, norm_sub_rev (g x) (g y), abs_sub_comm]
  have haa : (∫⁻ p, F p ∂μ.prod μ) = fractionalIntervalEnergy s L f := by
    rw [lintegral_prod _ hm.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro x hx
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro y hy
    simp only [F, g, intervalZeroExtension_of_mem f hx, intervalZeroExtension_of_mem f hy]
  have hab : (∫⁻ p, F p ∂μ.prod ν) = fractionalExteriorEnergy s L f := by
    rw [lintegral_prod _ hm.aemeasurable, fractionalExteriorEnergy_eq_zeroExtension]
    have he : ν = volume.restrict (Icc (0 : ℝ) L)ᶜ :=
      Measure.restrict_congr_set (Filter.EventuallyEq.compl Ioo_ae_eq_Icc)
    rw [he]
    rfl
  have hba : (∫⁻ p, F p ∂ν.prod μ) = fractionalExteriorEnergy s L f := by
    rw [lintegral_prod _ hm.aemeasurable]
    have hc : Measurable (Function.uncurry (fun x y : ℝ => F (x, y))) := hm
    rw [lintegral_lintegral_swap hc.aemeasurable]
    simpa only [hsym] using (lintegral_prod F (μ := μ) (ν := ν) hm.aemeasurable).symm.trans hab
  have hbb : (∫⁻ p, F p ∂ν.prod ν) = 0 := by
    rw [lintegral_prod _ hm.aemeasurable]
    have hzero : (∫⁻ x : ℝ in Aᶜ, ∫⁻ y : ℝ in Aᶜ, F (x, y)) =
        ∫⁻ x : ℝ in Aᶜ, ∫⁻ y : ℝ in Aᶜ, 0 := by
      apply setLIntegral_congr_fun measurableSet_Ioo.compl
      intro x hx
      apply setLIntegral_congr_fun measurableSet_Ioo.compl
      intro y hy
      simp [F, g, intervalZeroExtension_of_notMem f hx, intervalZeroExtension_of_notMem f hy]
    simpa only [lintegral_zero] using hzero
  have hv : volume = μ + ν := (Measure.restrict_add_restrict_compl measurableSet_Ioo).symm
  calc
    _ = ∫⁻ p, F p ∂volume.prod volume := (lintegral_prod F hm.aemeasurable).symm
    _ = _ := by
      rw [hv, Measure.add_prod, Measure.prod_add, Measure.prod_add]
      simp only [lintegral_add_measure, haa, hab, hba, hbb, add_zero]
      rw [two_mul, add_assoc]

/-- Exact decomposition for arbitrary interval `L²` representatives. -/
theorem fractionalLineEnergy_zeroExtension (s : ℝ) {L : ℝ} (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    fractionalLineEnergy s (intervalZeroExtension L f) =
      fractionalIntervalEnergy s L f + 2 * fractionalExteriorEnergy s L f := by
  let g := hf₂.aestronglyMeasurable.mk f
  have he : f =ᵐ[volume.restrict (Ioo 0 L)] g := hf₂.aestronglyMeasurable.ae_eq_mk
  rw [fractionalLineEnergy_congr (intervalZeroExtension_congr he),
    fractionalIntervalEnergy_congr he, fractionalExteriorEnergy_congr he]
  exact fractionalLineEnergy_zeroExtension_of_measurable s L g
    hf₂.aestronglyMeasurable.stronglyMeasurable_mk.measurable

/-- Zero extension preserves finite fractional energy below half, for arbitrary interval `L²` data. -/
theorem fractionalLineEnergy_zeroExtension_lt_top_iff {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    fractionalLineEnergy s (intervalZeroExtension L f) < ⊤ ↔ fractionalIntervalEnergy s L f < ⊤ := by
  rw [fractionalLineEnergy_zeroExtension s f hf₂]
  constructor
  · intro h
    exact lt_of_le_of_lt le_self_add h
  · intro h
    exact ENNReal.add_lt_top.mpr ⟨h, ENNReal.mul_lt_top (by norm_num)
      (fractionalExteriorEnergy_lt_top_of_interval hs hs₁ hL f hf₂ h)⟩

/-- Intrinsic physical fractional regularity on the interval. -/
def HasFractionalIntervalRegularity (s L : ℝ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 (volume.restrict (Ioo 0 L)) ∧ fractionalIntervalEnergy s L f < ⊤

/-- Physical fractional regularity on the real line. -/
def HasFractionalLineRegularity (s : ℝ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 volume ∧ fractionalLineEnergy s f < ⊤

/-- The actual zero extension identifies interval regularity with line regularity below half. -/
theorem hasFractionalLineRegularity_zeroExtension_iff {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) :
    HasFractionalLineRegularity s (intervalZeroExtension L f) ↔ HasFractionalIntervalRegularity s L f := by
  rw [HasFractionalLineRegularity, HasFractionalIntervalRegularity, memLp_intervalZeroExtension_iff]
  exact and_congr_right (fun hf => fractionalLineEnergy_zeroExtension_lt_top_iff hs hs₁ hL f hf)

end NLS.Fourier
