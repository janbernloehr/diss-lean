import NLS.Fourier.LineTemperedGalilean

/-! # Galilean invariance of full-line Fourier-Lebesgue spaces

This implements the Galilean statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory Complex
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p : ℝ≥0∞}

/-- Actual modulation and translation of an Lp equivalence class. -/
def lineLpModulationTranslation (ν a θ : ℝ) (f : Lp ℂ p (volume : Measure ℝ)) :
    Lp ℂ p (volume : Measure ℝ) :=
  (memLp_lineModulationTranslation ν a θ f p (Lp.memLp f)).toLp
    (lineModulationTranslation ν a θ f)

/-- The Lp class is represented by the literal physical formula almost everywhere. -/
theorem lineLpModulationTranslation_coeFn (ν a θ : ℝ)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    (lineLpModulationTranslation ν a θ f : ℝ → ℂ) =ᵐ[volume]
      lineModulationTranslation ν a θ f :=
  MemLp.coeFn_toLp _

/-- Every Lp norm, including infinity, is preserved exactly. -/
theorem norm_lineLpModulationTranslation (ν a θ : ℝ)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖lineLpModulationTranslation ν a θ f‖ = ‖f‖ := by
  rw [lineLpModulationTranslation,Lp.norm_toLp,eLpNorm_lineModulationTranslation,Lp.norm_def]

variable [Fact (1 ≤ p)]

/-- The transformed Lp representative gives the same actual physical distribution action. -/
theorem lineLpModulationTranslation_toTemperedDistribution (ν a θ : ℝ)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    (lineLpModulationTranslation ν a θ f : 𝓢'(ℝ,ℂ)) =
      lineTemperedModulationTranslation ν a θ (f : 𝓢'(ℝ,ℂ)) := by
  ext g
  rw [Lp.toTemperedDistribution_apply,lineTemperedModulationTranslation_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : ℝ, g x*lineModulationTranslation ν a θ f x := by
      apply integral_congr_ae
      filter_upwards [lineLpModulationTranslation_coeFn ν a θ f] with x hx
      rw [hx,smul_eq_mul]
    _ = ∫ x : ℝ, g (x+a)*lineModulationTranslation ν a θ f (x+a) :=
      (integral_add_right_eq_self _ a).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [lineSchwartzModulationTranslation_apply]
      simp only [lineModulationTranslation,smul_eq_mul,add_sub_cancel_right,sub_neg_eq_add]
      have he : ν*(x+a)+θ = ν*x+(ν*a+θ) := by ring
      rw [he]
      ring

/-- Full-line Fourier-Lebesgue membership is a property of the original tempered
 distribution: its actual Fourier transform has an Lp representative. -/
def IsLineFourierLebesgue (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : 𝓢'(ℝ,ℂ)) : Prop :=
  ∃ f : Lp ℂ p (volume : Measure ℝ), 𝓕 T = (f : 𝓢'(ℝ,ℂ))

/-- The Fourier Lp representative of an original distribution is unique. -/
theorem lineFourierLebesgue_representative_unique (T : 𝓢'(ℝ,ℂ))
    (f g : Lp ℂ p (volume : Measure ℝ))
    (hf : 𝓕 T = (f : 𝓢'(ℝ,ℂ))) (hg : 𝓕 T = (g : 𝓢'(ℝ,ℂ))) : f = g := by
  have he : (f : 𝓢'(ℝ,ℂ)) = (g : 𝓢'(ℝ,ℂ)) := hf.symm.trans hg
  have hk : f-g ∈ (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) p).ker := by
    change Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) p (f-g) = 0
    rw [map_sub,sub_eq_zero]
    exact he
  rw [Lp.ker_toTemperedDistributionCLM_eq_bot,Submodule.mem_bot] at hk
  exact sub_eq_zero.mp hk

/-- The physical Galilean action retains the original distribution's actual
Fourier Lp representative with exactly the same norm, also at infinity. -/
theorem exists_lineFourierLebesgue_galilean_representative (ν t : ℝ) (T : 𝓢'(ℝ,ℂ))
    (f : Lp ℂ p (volume : Measure ℝ)) (hf : 𝓕 T = (f : 𝓢'(ℝ,ℂ))) :
    ∃ g : Lp ℂ p (volume : Measure ℝ),
      𝓕 (lineTemperedGalilean ν t T) = (g : 𝓢'(ℝ,ℂ)) ∧ ‖g‖ = ‖f‖ := by
  refine ⟨lineLpModulationTranslation (-4*Real.pi*ν*t) (ν/(2*Real.pi)) (ν^2*t) f,?_,
    norm_lineLpModulationTranslation _ _ _ f⟩
  rw [fourier_lineTemperedGalilean,hf,lineLpModulationTranslation_toTemperedDistribution]

/-- Full-line Fourier-Lebesgue membership survives every real Galilean boost. -/
theorem IsLineFourierLebesgue.galilean {T : 𝓢'(ℝ,ℂ)} (hT : IsLineFourierLebesgue p T)
    (ν t : ℝ) : IsLineFourierLebesgue p (lineTemperedGalilean ν t T) := by
  obtain ⟨f,hf⟩ := hT
  obtain ⟨g,hg,_⟩ := exists_lineFourierLebesgue_galilean_representative ν t T f hf
  exact ⟨g,hg⟩

/-- Galilean symmetry preserves the full original Fourier-Lebesgue space in both directions. -/
theorem isLineFourierLebesgue_galilean_iff (ν t : ℝ) (T : 𝓢'(ℝ,ℂ)) :
    IsLineFourierLebesgue p (lineTemperedGalilean ν t T) ↔ IsLineFourierLebesgue p T := by
  constructor
  · intro h
    have hr := h.galilean (-ν) t
    rwa [lineTemperedGalilean_neg_apply] at hr
  · exact fun h => h.galilean ν t

end NLS.Fourier
