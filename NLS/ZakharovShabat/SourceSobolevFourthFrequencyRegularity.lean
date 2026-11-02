import NLS.ZakharovShabat.SourceSobolevFourthActionDerivatives

/-! # Full-domain regularity of the independently defined physical H₄ frequencies

The local action factors identify both frequency branches with one analytic
differential. In particular, the physical frequency is continuous across
closed actions in the original fractional source topology.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Each original physical frequency is real analytic throughout its full
H^(3/2) source, including the closed-action boundary. -/
theorem analyticAt_sobolevFourthFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a₀ : NativeFourthSobolevSource) (n : ℤ) :
    AnalyticAt ℝ (fun a => D.sobolevFourthFrequency a n) a₀ := by
  obtain ⟨V,T,H,hV,ha₀,_,hmap,hH,_,hfreq⟩ := D.exists_sobolevFourth_action_factor_with_frequencies a₀
  let I : NativeFourthSobolevSource → FourthSobolevActions :=
    fun a => fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)
  have hI : AnalyticAt ℝ I a₀ :=
    (analyticOnNhd_fourthSobolevActions _ (mem_univ _)).comp
      (D.originalWeightedRealMap_analytic fourthSobolevSpectralWeight a₀ (mem_univ _))
  have hdH : AnalyticAt ℝ (fderiv ℂ H) (I a₀) :=
    (hH _ (hmap ha₀)).fderiv.restrictScalars (𝕜 := ℝ)
  let E := (ContinuousLinearMap.apply ℂ ℂ (fourthSobolevActionDirection n)).restrictScalars ℝ
  have hF : AnalyticAt ℝ (fun a => fderiv ℂ H (I a) (fourthSobolevActionDirection n)) a₀ :=
    (E.analyticAt _).comp (hdH.comp hI)
  apply hF.congr
  have hev : ∀ᶠ a in 𝓝 a₀, D.originalWeightedRealMap fourthSobolevSpectralWeight a ∈ V :=
    (D.originalWeightedRealMap_continuous fourthSobolevSpectralWeight).continuousAt.tendsto.eventually
      (hV.mem_nhds ha₀)
  filter_upwards [hev] with a ha
  exact (hfreq a ha n).symm

/-- The independent physical frequencies are continuous in the full native
fractional norm, without excluding collapsed gaps. -/
theorem continuous_sobolevFourthFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) (n : ℤ) :
    Continuous (fun a : NativeFourthSobolevSource => D.sobolevFourthFrequency a n) :=
  continuous_iff_continuousAt.mpr fun a => (D.analyticAt_sobolevFourthFrequency a n).continuousAt

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
