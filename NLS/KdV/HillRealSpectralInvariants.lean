import NLS.KdV.HillDirichletSpectralLocalFlow

/-! The complete discriminant data as an invariant on the actual
physical real mean-zero Banach source, with the unchanged native ODE. -/
noncomputable section
open Set
namespace NLS.KdV

theorem hillRealMeanZeroInclusion_injective : Function.Injective hillRealMeanZeroInclusion := by
  intro p q h
  exact Subtype.ext (Subtype.ext h)

theorem hillRealMeanZeroProjection_subtype (q : HillRealMeanZeroSource) :
    hillRealMeanZeroProjection (hillRealMeanZeroInclusion q)=q := by
  apply hillRealMeanZeroInclusion_injective
  exact hillRealMeanZeroProjection_inclusion _ q.property q.val.property

theorem hasDerivAt_hillRealMeanZeroInclusion_comp (γ : ℝ → HillRealMeanZeroSource)
    (v : HillRealMeanZeroSource) (t : ℝ) (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun τ => hillRealMeanZeroInclusion (γ τ)) (hillRealMeanZeroInclusion v) t := by
  have hi := @ContinuousLinearMap.hasFDerivAt ℝ inferInstance
    HillRealMeanZeroSource (inferInstance : NormedAddCommGroup HillRealMeanZeroSource).toAddCommGroup
    (inferInstance : NormedSpace ℝ HillRealMeanZeroSource).toModule inferInstance
    PeriodOneHminusOne (inferInstance : NormedAddCommGroup PeriodOneHminusOne).toAddCommGroup
    (inferInstance : NormedSpace ℝ PeriodOneHminusOne).toModule inferInstance
    hillRealMeanZeroInclusion (γ t)
  exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := HillRealMeanZeroSource) (E := PeriodOneHminusOne) t hi hγ

def hillRealDiscriminantData (q : HillRealMeanZeroSource) : ℂ → ℂ :=
  hillHminusDiscriminant (hillRealMeanZeroInclusion q)

theorem hillRealDiscriminantData_eq_on_integralCurve (k : ℕ+)
    (γ : ℝ → HillRealMeanZeroSource) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillRealDirichletSpectralVector k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    hillRealDiscriminantData (γ u)=hillRealDiscriminantData (γ v) := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ => hillRealMeanZeroInclusion (γ τ))
        (hillHminusDirichletSpectralVector k (hillRealMeanZeroInclusion (γ t))) t := by
    simpa only [hillRealDirichletSpectralVector_inclusion] using
      hasDerivAt_hillRealMeanZeroInclusion_comp γ _ t (hγ t ht)
  funext E
  exact hillHminusDiscriminant_eq_on_spectral_integralCurve k
    (fun τ => hillRealMeanZeroInclusion (γ τ)) a b hd u v hu hv E

end NLS.KdV
