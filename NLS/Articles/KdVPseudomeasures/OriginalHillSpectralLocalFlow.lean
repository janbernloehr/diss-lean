import NLS.KdV.HillDirichletSpectralLocalFlow
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSpectralFirstVariation
import NLS.Articles.KdVPseudomeasures.OriginalHminusOneCompactness

/-! Actual local indexed spectral curves through every original physical
H-minus-one potential. Their values stay in its exact original isospectral
set on the constructed interval. Global continuation remains separate. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def originalHillRealMeanZeroSource (q : OriginalHminusOnePotential) : HillRealMeanZeroSource :=
  ⟨⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_mean_zero q⟩,
    originalPeriodOneCoefficients_real q⟩

theorem originalHillRealMeanZeroSource_inclusion (q : OriginalHminusOnePotential) :
    hillRealMeanZeroInclusion (originalHillRealMeanZeroSource q)=originalPeriodOneCoefficients q := rfl

theorem exists_original_Hill_spectral_isospectral_localCurve (k : ℕ+)
    (q : OriginalHminusOnePotential) :
    ∃ γ : ℝ → OriginalHminusOnePotential, γ 0=q ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun τ => originalPeriodOneCoefficients (γ τ))
        (hillHminusDirichletSpectralVector k (originalPeriodOneCoefficients (γ t))) t) ∧
      ∀ t ∈ Ioo (-ε) ε, γ t ∈ originalIsospectralSet q := by
  obtain ⟨α,hα,hr,ε,hε,hder,hiso⟩ :=
    exists_hillHminusDirichletSpectral_isospectral_integralCurve k (originalHillRealMeanZeroSource q)
  let γ : ℝ → OriginalHminusOnePotential := fun t =>
    ⟨periodOneOriginal (α t),(periodOneOriginal_source_iff (α t)).mpr (hr t)⟩
  have he (t : ℝ) : originalPeriodOneCoefficients (γ t)=α t :=
    periodOneOriginalExtract_original (α t)
  have hγ₀ : γ 0=q := by
    apply Subtype.ext
    change periodOneOriginal (α 0)=q.val
    rw [hα,originalHillRealMeanZeroSource_inclusion,periodOneOriginal_originalPeriodOneCoefficients]
  refine ⟨γ,hγ₀,ε,hε,?_,?_⟩
  · intro t ht
    simpa only [he] using hder t ht
  · intro t ht
    apply (mem_originalIsospectralSet_iff_discriminant_eq q (γ t)).mpr
    funext E
    change hillHminusDiscriminant (originalPeriodOneCoefficients (γ t)) E=
      hillHminusDiscriminant (originalPeriodOneCoefficients q) E
    simpa only [he,originalHillRealMeanZeroSource_inclusion] using hiso t ht E

end NLS.Articles.KdVPseudomeasures
