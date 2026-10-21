import NLS.Fourier.LineAngularSchwartz

/-! # Galilean covariance of actual tempered distributions

This implements the Galilean statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory Complex
open scoped SchwartzMap FourierTransform
namespace NLS.Fourier

/-- Physical translation on tempered distributions, by the exact dual action on tests. -/
def lineTemperedTranslation (a : ℝ) : 𝓢'(ℝ,ℂ) →L[ℂ] 𝓢'(ℝ,ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ (SchwartzMap.compSubConstCLM ℂ (-a))

@[simp] theorem lineTemperedTranslation_apply (a : ℝ) (T : 𝓢'(ℝ,ℂ)) (g : 𝓢(ℝ,ℂ)) :
    lineTemperedTranslation a T g = T (SchwartzMap.compSubConstCLM ℂ (-a) g) := rfl

/-- Actual physical modulation after translation, using Mathlib's smooth distribution product. -/
def lineTemperedModulationTranslation (ν a θ : ℝ) : 𝓢'(ℝ,ℂ) →L[ℂ] 𝓢'(ℝ,ℂ) :=
  (TemperedDistribution.smulLeftCLM ℂ (lineAngularPhase ν θ)).comp (lineTemperedTranslation a)

/-- The weak action retains the exact shifted phase and spatial argument. -/
theorem lineTemperedModulationTranslation_apply (ν a θ : ℝ)
    (T : 𝓢'(ℝ,ℂ)) (g : 𝓢(ℝ,ℂ)) :
    lineTemperedModulationTranslation ν a θ T g =
      T (lineSchwartzModulationTranslation ν (-a) (ν*a+θ) g) := by
  simp only [lineTemperedModulationTranslation,ContinuousLinearMap.comp_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,lineTemperedTranslation_apply]
  congr 1
  ext x
  rw [SchwartzMap.compSubConstCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (lineAngularPhase_hasTemperateGrowth ν θ),
    lineSchwartzModulationTranslation_apply]
  simp only [lineAngularPhase,lineModulationTranslation,smul_eq_mul,sub_neg_eq_add]
  congr 2
  push_cast
  ring

/-- The exact physical Fourier intertwining law holds for every tempered distribution. -/
theorem fourier_lineTemperedModulationTranslation (ν a θ : ℝ) (T : 𝓢'(ℝ,ℂ)) :
    𝓕 (lineTemperedModulationTranslation ν a θ T) =
      lineTemperedModulationTranslation (-2*Real.pi*a) (ν/(2*Real.pi)) (ν*a+θ) (𝓕 T) := by
  ext g
  rw [TemperedDistribution.fourier_apply,lineTemperedModulationTranslation_apply,
    lineTemperedModulationTranslation_apply,TemperedDistribution.fourier_apply]
  congr 1
  ext x
  rw [lineSchwartzModulationTranslation_apply,fourier_lineSchwartzModulationTranslation]
  unfold lineModulationTranslation
  have hfreq : x-(-2*Real.pi*a)/(2*Real.pi) = x+a := by field_simp; ring
  have hphase : (-2*Real.pi*a)*(-(ν/(2*Real.pi)))+
      ((-2*Real.pi*a)*(ν/(2*Real.pi))+(ν*a+θ))-
      2*Real.pi*(-(ν/(2*Real.pi)))*x = ν*x+(ν*a+θ) := by field_simp; ring
  rw [hfreq,hphase,sub_neg_eq_add]

/-- The full-line Galilean action on actual tempered distributions. -/
def lineTemperedGalilean (ν t : ℝ) : 𝓢'(ℝ,ℂ) →L[ℂ] 𝓢'(ℝ,ℂ) :=
  lineTemperedModulationTranslation ν (2*ν*t) (-(ν^2)*t)

/-- The physical Galilean action on tests has the exact simplified phase. -/
theorem lineTemperedGalilean_apply (ν t : ℝ) (T : 𝓢'(ℝ,ℂ)) (g : 𝓢(ℝ,ℂ)) :
    lineTemperedGalilean ν t T g =
      T (lineSchwartzModulationTranslation ν (-(2*ν*t)) (ν^2*t) g) := by
  rw [lineTemperedGalilean,lineTemperedModulationTranslation_apply]
  congr 3
  ring

/-- The opposite boost is an actual inverse on every tempered distribution. -/
theorem lineTemperedGalilean_neg_apply (ν t : ℝ) (T : 𝓢'(ℝ,ℂ)) :
    lineTemperedGalilean (-ν) t (lineTemperedGalilean ν t T) = T := by
  ext g
  rw [lineTemperedGalilean_apply,lineTemperedGalilean_apply]
  congr 1
  ext x
  rw [lineSchwartzModulationTranslation_apply]
  unfold lineModulationTranslation
  rw [lineSchwartzModulationTranslation_apply]
  unfold lineModulationTranslation
  have hx : (x-(-(2*ν*t)))-(-(2*(-ν)*t)) = x := by ring
  have he : (ν*x+ν^2*t)+((-ν)*(x-(-(2*ν*t)))+(-ν)^2*t) = 0 := by ring
  rw [hx,← mul_assoc,← Complex.exp_add,← add_mul,← Complex.ofReal_add,he]
  simp

/-- Exact Fourier covariance of the physical Galilean action for all distributions. -/
theorem fourier_lineTemperedGalilean (ν t : ℝ) (T : 𝓢'(ℝ,ℂ)) :
    𝓕 (lineTemperedGalilean ν t T) =
      lineTemperedModulationTranslation (-4*Real.pi*ν*t) (ν/(2*Real.pi)) (ν^2*t) (𝓕 T) := by
  rw [lineTemperedGalilean,fourier_lineTemperedModulationTranslation]
  congr 2 <;> ring

end NLS.Fourier
