import NLS.Fourier.IntervalDilation
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Fourier formulas for physical Galilean boosts

This implements the Galilean statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory Complex
open scoped ENNReal FourierTransform
namespace NLS.Fourier

/-- A full-line spatial translation and an arbitrary real angular modulation. -/
def lineModulationTranslation (ν a θ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((ν*x+θ:ℝ)*Complex.I)*f (x-a)

/-- The exact full-line Fourier transform, retaining the angular-to-cyclic factor 2π. -/
theorem fourier_lineModulationTranslation (ν a θ : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (lineModulationTranslation ν a θ f) ξ =
      Complex.exp ((ν*a+θ-2*Real.pi*a*ξ:ℝ)*Complex.I)*𝓕 f (ξ-ν/(2*Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_add_right_eq_self
    (fun x : ℝ => Complex.exp ((-2*Real.pi*x*ξ:ℝ)*Complex.I)*
      lineModulationTranslation ν a θ f x) a]
  rw [Real.fourier_real_eq_integral_exp_smul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  have he : -2*Real.pi*(y+a)*ξ+(ν*(y+a)+θ) =
      (ν*a+θ-2*Real.pi*a*ξ)+(-2*Real.pi*y*(ξ-ν/(2*Real.pi))) := by
    field_simp
    ring
  simp only [lineModulationTranslation,add_sub_cancel_right,smul_eq_mul,
    ← mul_assoc,← Complex.exp_add,← add_mul,← Complex.ofReal_add]
  rw [he]

/-- Full-line translation preserves every extended Lp seminorm, including infinity. -/
theorem eLpNorm_line_translation (F : ℝ → ℂ) (a : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x : ℝ => F (x-a)) p volume = eLpNorm F p volume := by
  have hm := measurePreserving_add_right (volume : Measure ℝ) (-a)
  have he : MeasurableEmbedding (fun x : ℝ => x + (-a)) :=
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
  have h := he.eLpNorm_map_measure (g := F) (p := p) (μ := volume)
  rw [hm.map_eq] at h
  simpa only [Function.comp_def,sub_eq_add_neg] using h.symm

/-- Arbitrary angular modulation and translation preserve the physical Lp seminorm. -/
theorem eLpNorm_lineModulationTranslation (ν a θ : ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (lineModulationTranslation ν a θ f) p volume = eLpNorm f p volume := by
  calc
    _ = eLpNorm (fun x : ℝ => f (x-a)) p volume := by
      apply eLpNorm_congr_norm_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [lineModulationTranslation,norm_mul,norm_exp_ofReal_mul_I,one_mul])
    _ = _ := eLpNorm_line_translation _ _ _

/-- The transformed function retains actual Lp membership and measurability. -/
theorem memLp_lineModulationTranslation (ν a θ : ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞)
    (hf : MemLp f p volume) : MemLp (lineModulationTranslation ν a θ f) p volume := by
  have hm : MeasurePreserving (fun x : ℝ => x-a) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-a)
  have hs := hf.comp_measurePreserving hm
  have hc : Continuous (fun x : ℝ => Complex.exp ((ν*x+θ:ℝ)*Complex.I)) := by fun_prop
  refine ⟨hc.aestronglyMeasurable.mul hs.aestronglyMeasurable,?_⟩
  rw [eLpNorm_lineModulationTranslation]
  exact hf.eLpNorm_lt_top

/-- Arbitrary real modulation and translation preserve the Fourier Lp seminorm. -/
theorem eLpNorm_fourier_lineModulationTranslation
    (ν a θ : ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (𝓕 (lineModulationTranslation ν a θ f)) p volume =
      eLpNorm (𝓕 f) p volume := by
  calc
    _ = eLpNorm (fun ξ : ℝ => 𝓕 f (ξ-ν/(2*Real.pi))) p volume := by
      apply eLpNorm_congr_norm_ae
      exact Filter.Eventually.of_forall (fun ξ => by
        rw [fourier_lineModulationTranslation,norm_mul,norm_exp_ofReal_mul_I,one_mul])
    _ = _ := eLpNorm_line_translation _ _ _

/-- Fourier Lp membership is retained, with the exact transformed Fourier function. -/
theorem memLp_fourier_lineModulationTranslation
    (ν a θ : ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞) (hf : MemLp (𝓕 f) p volume) :
    MemLp (𝓕 (lineModulationTranslation ν a θ f)) p volume := by
  have h := memLp_lineModulationTranslation (-2*Real.pi*a) (ν/(2*Real.pi))
    (ν*a+θ) (𝓕 f) p hf
  have he : 𝓕 (lineModulationTranslation ν a θ f) =
      lineModulationTranslation (-2*Real.pi*a) (ν/(2*Real.pi)) (ν*a+θ) (𝓕 f) := by
    funext ξ
    rw [fourier_lineModulationTranslation]
    unfold lineModulationTranslation
    congr 3
    push_cast
    ring
  rwa [he]

/-- The physical Galilean slice, with exactly the source phase and spatial speed. -/
def lineGalileanSlice (ν t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  lineModulationTranslation ν (2*ν*t) (-(ν^2)*t) f

/-- Exact Fourier formula for a physical Galilean slice. -/
theorem fourier_lineGalileanSlice (ν t : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (lineGalileanSlice ν t f) ξ =
      Complex.exp ((ν^2*t-4*Real.pi*ν*t*ξ:ℝ)*Complex.I)*𝓕 f (ξ-ν/(2*Real.pi)) := by
  rw [lineGalileanSlice,fourier_lineModulationTranslation]
  congr 3
  push_cast
  ring

/-- Galilean slices preserve every Fourier Lp seminorm. -/
theorem eLpNorm_fourier_lineGalileanSlice (ν t : ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (𝓕 (lineGalileanSlice ν t f)) p volume = eLpNorm (𝓕 f) p volume :=
  eLpNorm_fourier_lineModulationTranslation ν (2*ν*t) (-(ν^2)*t) f p

/-- Actual Fourier Lp membership survives the physical Galilean slice. -/
theorem memLp_fourier_lineGalileanSlice (ν t : ℝ) (f : ℝ → ℂ) (p : ℝ≥0∞)
    (hf : MemLp (𝓕 f) p volume) : MemLp (𝓕 (lineGalileanSlice ν t f)) p volume :=
  memLp_fourier_lineModulationTranslation ν (2*ν*t) (-(ν^2)*t) f p hf

end NLS.Fourier
