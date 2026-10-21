import NLS.Fourier.CriticalFrequencyMeasure
import NLS.Fourier.LineTemperedNLSScaling

/-! # A complete critical homogeneous Sobolev space of distributions

This implements the critical full-line dilation statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier

/-- Complete spectral model for the critical homogeneous negative-half space.
The Fourier density is |xi| times this L2 representative. -/
abbrev CriticalHomogeneousSobolev := Lp ℂ 2 criticalFrequencyMeasure

/-- The critical spectral model is a complete normed space. -/
theorem criticalHomogeneousSobolev_complete : CompleteSpace CriticalHomogeneousSobolev :=
  inferInstance

/-- Physical distributions are recovered using the actual inverse Fourier transform. -/
def criticalHomogeneousSobolevDistribution (f : CriticalHomogeneousSobolev) : 𝓢'(ℝ,ℂ) :=
  𝓕⁻ (f : 𝓢'(ℝ,ℂ))

/-- Continuous linear embedding of the complete critical space into actual distributions. -/
def criticalHomogeneousSobolevDistributionCLM : CriticalHomogeneousSobolev →L[ℂ] 𝓢'(ℝ,ℂ) :=
  (FourierTransform.fourierCLE ℂ 𝓢'(ℝ,ℂ)).symm.toContinuousLinearMap.comp
    (Lp.toTemperedDistributionCLM ℂ criticalFrequencyMeasure 2)

@[simp] theorem criticalHomogeneousSobolevDistributionCLM_apply (f : CriticalHomogeneousSobolev) :
    criticalHomogeneousSobolevDistributionCLM f = criticalHomogeneousSobolevDistribution f := rfl

/-- The physical distribution depends continuously on its critical Sobolev representative. -/
theorem continuous_criticalHomogeneousSobolevDistribution :
    Continuous criticalHomogeneousSobolevDistribution := criticalHomogeneousSobolevDistributionCLM.continuous

/-- The actual Fourier transform is the weighted L2 integral distribution. -/
theorem fourier_criticalHomogeneousSobolevDistribution (f : CriticalHomogeneousSobolev) :
    𝓕 (criticalHomogeneousSobolevDistribution f) = (f : 𝓢'(ℝ,ℂ)) := by
  exact FourierTransform.fourier_fourierInv_eq _

/-- No two spectral representatives describe the same physical distribution. -/
theorem criticalHomogeneousSobolevDistribution_injective :
    Function.Injective criticalHomogeneousSobolevDistribution := by
  intro f g h
  have he := congrArg (fun T : 𝓢'(ℝ,ℂ) => 𝓕 T) h
  simp only [fourier_criticalHomogeneousSobolevDistribution] at he
  have hk : f-g ∈ (Lp.toTemperedDistributionCLM ℂ criticalFrequencyMeasure 2).ker := by
    change Lp.toTemperedDistributionCLM ℂ criticalFrequencyMeasure 2 (f-g) = 0
    rw [map_sub,sub_eq_zero]
    exact he
  rw [Lp.ker_toTemperedDistributionCLM_eq_bot,Submodule.mem_bot] at hk
  exact sub_eq_zero.mp hk

/-- The literal critical spectral dilation preserves the extended L2 norm. -/
theorem eLpNorm_criticalFrequency_scaling {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) :
    eLpNorm (fun ξ => (c:ℂ)⁻¹*f (c⁻¹*ξ)) 2 criticalFrequencyMeasure =
      eLpNorm f 2 criticalFrequencyMeasure := by
  have hm := measurePreserving_criticalFrequency_dilation (inv_pos.mpr hc)
  have he := (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc.ne')).measurableEmbedding.eLpNorm_map_measure
    (g := f) (p := (2:ℝ≥0∞)) (μ := criticalFrequencyMeasure)
  change eLpNorm f 2 (Measure.map (fun ξ : ℝ => c⁻¹*ξ) criticalFrequencyMeasure) =
    eLpNorm (f ∘ (fun ξ : ℝ => c⁻¹*ξ)) 2 criticalFrequencyMeasure at he
  rw [hm.map_eq] at he
  have hs : ((ENNReal.ofReal c⁻¹⁻¹)^2)^((1/(2:ℝ≥0∞)).toReal) = ENNReal.ofReal c := by
    simp only [inv_inv,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  change eLpNorm ((c:ℂ)⁻¹ • (f ∘ (fun ξ => c⁻¹*ξ))) 2 criticalFrequencyMeasure = _
  rw [eLpNorm_const_smul,← he,eLpNorm_smul_measure_of_ne_top (by norm_num),hs]
  have hn : (‖(c:ℂ)⁻¹‖₊ : ℝ≥0∞) = ENNReal.ofReal c⁻¹ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ‖(c:ℂ)⁻¹‖ = _
    rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hc.le]
  simp only [enorm_eq_nnnorm,hn,smul_eq_mul,← mul_assoc]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),inv_mul_cancel₀ hc.ne']
  simp

/-- Critical spectral dilation acts on actual L2 equivalence classes. -/
theorem memLp_criticalFrequency_scaling {c : ℝ} (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) :
    MemLp (fun ξ => (c:ℂ)⁻¹*f (c⁻¹*ξ)) 2 criticalFrequencyMeasure := by
  have hf := (Lp.memLp f).smul_measure
    (c := (ENNReal.ofReal c⁻¹⁻¹)^2) (by finiteness)
  exact (hf.comp_measurePreserving
    (measurePreserving_criticalFrequency_dilation (inv_pos.mpr hc))).const_smul (c:ℂ)⁻¹

/-- The critical L2 representative of a physical NLS dilation. -/
def criticalHomogeneousSobolevScaling (c : ℝ) (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) : CriticalHomogeneousSobolev :=
  (memLp_criticalFrequency_scaling hc f).toLp (fun ξ => (c:ℂ)⁻¹*f (c⁻¹*ξ))

/-- The representative retains the literal spectral scaling almost everywhere. -/
theorem criticalHomogeneousSobolevScaling_coeFn (c : ℝ) (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) :
    (criticalHomogeneousSobolevScaling c hc f : ℝ → ℂ) =ᵐ[criticalFrequencyMeasure]
      (fun ξ => (c:ℂ)⁻¹*f (c⁻¹*ξ)) := MemLp.coeFn_toLp _

/-- The completed critical model has exactly invariant norm under NLS dilation. -/
theorem norm_criticalHomogeneousSobolevScaling (c : ℝ) (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) : ‖criticalHomogeneousSobolevScaling c hc f‖ = ‖f‖ := by
  rw [criticalHomogeneousSobolevScaling,Lp.norm_toLp,eLpNorm_criticalFrequency_scaling hc,
    Lp.norm_def]

/-- The L2 norm is exactly the critical homogeneous energy of the Fourier density. -/
theorem homogeneousSpectralEnergy_criticalDensity (f : CriticalHomogeneousSobolev) :
    homogeneousSpectralEnergy (-(1:ℝ)/2) (fun ξ => (‖ξ‖:ℂ)*f ξ) =
      ENNReal.ofReal (‖f‖^2) := by
  have henergy : homogeneousSpectralEnergy (-(1:ℝ)/2) (fun ξ => (‖ξ‖:ℂ)*f ξ) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖f ξ‖^2) ∂criticalFrequencyMeasure := by
    rw [homogeneousSpectralEnergy,lintegral_criticalFrequencyMeasure]
    apply lintegral_congr
    intro ξ
    norm_num only [show (2:ℝ)*(-(1:ℝ)/2) = -1 by norm_num,Real.rpow_neg_one]
    rw [← Real.norm_eq_abs ξ]
    by_cases hξ : ξ = 0
    · simp [hξ]
    · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg ξ),mul_pow]
      rw [ENNReal.ofReal_mul (sq_nonneg _),← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
  rw [henergy,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm,Lp.enorm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num only [show (1/(2:ℝ))*2 = 1 by norm_num,ENNReal.rpow_one]
  apply lintegral_congr
  intro ξ
  rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm,ENNReal.rpow_two]

/-- The weighted spectral distribution is the literal Fourier density against Lebesgue measure. -/
theorem criticalHomogeneousSobolev_fourier_apply (f : CriticalHomogeneousSobolev)
    (g : 𝓢(ℝ,ℂ)) :
    𝓕 (criticalHomogeneousSobolevDistribution f) g =
      ∫ ξ : ℝ, g ξ*((‖ξ‖:ℂ)*f ξ) := by
  rw [fourier_criticalHomogeneousSobolevDistribution,Lp.toTemperedDistribution_apply]
  change (∫ ξ : ℝ, g ξ • f ξ ∂volume.withDensity (fun ξ : ℝ => ENNReal.ofReal ‖ξ‖)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [ENNReal.toReal_ofReal (norm_nonneg _),smul_eq_mul,Complex.real_smul]
  ring

/-- Spectral L2 dilation agrees with the actual dilation of its distribution. -/
theorem criticalHomogeneousSobolevScaling_toTemperedDistribution (c : ℝ) (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) :
    (criticalHomogeneousSobolevScaling c hc f : 𝓢'(ℝ,ℂ)) =
      distributionDilation c⁻¹ (inv_ne_zero hc.ne') (f : 𝓢'(ℝ,ℂ)) := by
  ext g
  rw [Lp.toTemperedDistribution_apply,distributionDilation_apply,Lp.toTemperedDistribution_apply]
  simp only [Complex.ofReal_inv,inv_inv]
  calc
    _ = ∫ ξ : ℝ, g ξ*((c:ℂ)⁻¹*f (c⁻¹*ξ)) ∂criticalFrequencyMeasure := by
      apply integral_congr_ae
      filter_upwards [criticalHomogeneousSobolevScaling_coeFn c hc f] with ξ hξ
      rw [hξ,smul_eq_mul]
    _ = ∫ ξ : ℝ, g (c*(c⁻¹*ξ))*((c:ℂ)⁻¹*f (c⁻¹*ξ)) ∂criticalFrequencyMeasure := by
      simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
    _ = ∫ ξ : ℝ, g (c*ξ)*((c:ℂ)⁻¹*f ξ)
        ∂((ENNReal.ofReal c⁻¹⁻¹)^2 • criticalFrequencyMeasure) := by
      exact (measurePreserving_criticalFrequency_dilation (inv_pos.mpr hc)).integral_comp
        (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc.ne')).measurableEmbedding
        (fun ξ : ℝ => g (c*ξ)*((c:ℂ)⁻¹*f ξ))
    _ = _ := by
      rw [integral_smul_measure]
      simp only [inv_inv,ENNReal.toReal_pow,ENNReal.toReal_ofReal hc.le,
        schwartzDilationCLM_apply,smul_eq_mul,Complex.real_smul]
      have he : (fun ξ : ℝ => g (c*ξ)*((c:ℂ)⁻¹*f ξ)) =
          (fun ξ : ℝ => (c:ℂ)⁻¹*(g (c*ξ)*f ξ)) := by funext ξ; ring
      rw [he,integral_const_mul]
      push_cast
      field_simp

/-- The completed model's scaling is exactly physical NLS scaling on the same distribution. -/
theorem criticalHomogeneousSobolevDistribution_scaling (c : ℝ) (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) :
    criticalHomogeneousSobolevDistribution (criticalHomogeneousSobolevScaling c hc f) =
      lineTemperedNLSScaling c hc (criticalHomogeneousSobolevDistribution f) := by
  have he : 𝓕 (criticalHomogeneousSobolevDistribution (criticalHomogeneousSobolevScaling c hc f)) =
      𝓕 (lineTemperedNLSScaling c hc (criticalHomogeneousSobolevDistribution f)) := by
    rw [fourier_criticalHomogeneousSobolevDistribution,fourier_lineTemperedNLSScaling,
      fourier_criticalHomogeneousSobolevDistribution,
      criticalHomogeneousSobolevScaling_toTemperedDistribution]
  have h := congrArg (fun T : 𝓢'(ℝ,ℂ) => 𝓕⁻ T) he
  simpa only [FourierTransform.fourierInv_fourier_eq] using h

/-- Applying the opposite positive dilation recovers the same critical-space element. -/
theorem criticalHomogeneousSobolevScaling_inverse (c : ℝ) (hc : 0 < c)
    (f : CriticalHomogeneousSobolev) :
    criticalHomogeneousSobolevScaling c⁻¹ (inv_pos.mpr hc)
      (criticalHomogeneousSobolevScaling c hc f) = f := by
  apply criticalHomogeneousSobolevDistribution_injective
  rw [criticalHomogeneousSobolevDistribution_scaling,criticalHomogeneousSobolevDistribution_scaling,
    lineTemperedNLSScaling_inverse]

/-- The critical-space dilation preserves addition. -/
theorem criticalHomogeneousSobolevScaling_add (c : ℝ) (hc : 0 < c)
    (f g : CriticalHomogeneousSobolev) :
    criticalHomogeneousSobolevScaling c hc (f+g) =
      criticalHomogeneousSobolevScaling c hc f + criticalHomogeneousSobolevScaling c hc g := by
  apply criticalHomogeneousSobolevDistribution_injective
  have ha (u v : CriticalHomogeneousSobolev) : criticalHomogeneousSobolevDistribution (u+v) =
      criticalHomogeneousSobolevDistribution u + criticalHomogeneousSobolevDistribution v :=
    criticalHomogeneousSobolevDistributionCLM.map_add u v
  simp only [criticalHomogeneousSobolevDistribution_scaling,ha,map_add]

/-- The critical-space dilation preserves complex scalar multiplication. -/
theorem criticalHomogeneousSobolevScaling_smul (c : ℝ) (hc : 0 < c)
    (z : ℂ) (f : CriticalHomogeneousSobolev) :
    criticalHomogeneousSobolevScaling c hc (z • f) = z • criticalHomogeneousSobolevScaling c hc f := by
  apply criticalHomogeneousSobolevDistribution_injective
  have hs (u : CriticalHomogeneousSobolev) : criticalHomogeneousSobolevDistribution (z • u) =
      z • criticalHomogeneousSobolevDistribution u :=
    criticalHomogeneousSobolevDistributionCLM.map_smul z u
  simp only [criticalHomogeneousSobolevDistribution_scaling,hs,map_smul]

/-- Physical NLS scaling is a surjective complex linear isometry of the complete critical space. -/
def criticalHomogeneousSobolevScalingEquiv (c : ℝ) (hc : 0 < c) :
    CriticalHomogeneousSobolev ≃ₗᵢ[ℂ] CriticalHomogeneousSobolev where
  toFun := criticalHomogeneousSobolevScaling c hc
  invFun := criticalHomogeneousSobolevScaling c⁻¹ (inv_pos.mpr hc)
  left_inv := criticalHomogeneousSobolevScaling_inverse c hc
  right_inv f := by
    simpa only [inv_inv] using criticalHomogeneousSobolevScaling_inverse c⁻¹ (inv_pos.mpr hc) f
  map_add' := criticalHomogeneousSobolevScaling_add c hc
  map_smul' := criticalHomogeneousSobolevScaling_smul c hc
  norm_map' := norm_criticalHomogeneousSobolevScaling c hc

/-- Critical homogeneous membership is a property of the original physical distribution. -/
def IsCriticalHomogeneousSobolev (T : 𝓢'(ℝ,ℂ)) : Prop :=
  ∃ f : CriticalHomogeneousSobolev, criticalHomogeneousSobolevDistribution f = T

/-- Every critical distribution retains a representative with exactly the same norm. -/
theorem exists_criticalHomogeneousSobolev_scaling_representative (c : ℝ) (hc : 0 < c)
    (T : 𝓢'(ℝ,ℂ)) (f : CriticalHomogeneousSobolev) (hf : criticalHomogeneousSobolevDistribution f = T) :
    ∃ g : CriticalHomogeneousSobolev,
      criticalHomogeneousSobolevDistribution g = lineTemperedNLSScaling c hc T ∧ ‖g‖ = ‖f‖ := by
  refine ⟨criticalHomogeneousSobolevScaling c hc f,?_,norm_criticalHomogeneousSobolevScaling c hc f⟩
  rw [criticalHomogeneousSobolevDistribution_scaling,hf]

/-- Critical membership is invariant in both directions under the actual physical scaling. -/
theorem isCriticalHomogeneousSobolev_scaling_iff (c : ℝ) (hc : 0 < c) (T : 𝓢'(ℝ,ℂ)) :
    IsCriticalHomogeneousSobolev (lineTemperedNLSScaling c hc T) ↔ IsCriticalHomogeneousSobolev T := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨g,hg,_⟩ := exists_criticalHomogeneousSobolev_scaling_representative c⁻¹ (inv_pos.mpr hc) _ f hf
    rw [lineTemperedNLSScaling_inverse] at hg
    exact ⟨g,hg⟩
  · rintro ⟨f,hf⟩
    obtain ⟨g,hg,_⟩ := exists_criticalHomogeneousSobolev_scaling_representative c hc T f hf
    exact ⟨g,hg⟩

end NLS.Fourier
