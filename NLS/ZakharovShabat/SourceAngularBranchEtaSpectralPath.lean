import NLS.ComplexAnalysis.HolomorphicPathPullback
import NLS.ZakharovShabat.SourceAngularBranchEtaRepresentative
import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathModel

/-! # Literal spectral path integrals of complex branch representatives

Map a regular angle path into the spectral plane. If the continued full
root agrees with its cosine lift along the interior, the actual eta
differential is automatically integrable and its literal spectral-path
integral equals the analytic branch representative. Endpoint zeros
are allowed without any endpoint equality of the differential.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem continuous_sourceAngularBranchCosinePoint_spectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (δ : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    Continuous (fun e => sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ)) := by
  change Continuous (fun e => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m + δ ψ * Complex.cos e)
  exact continuous_const.add (continuous_const.mul Complex.continuous_cos)

namespace SourceAngularBranchCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {δ : CoeffPair p → ℂ}
  {W V : Set (CoeffPair p)} {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

theorem etaRepresentative_eq_spectral_pathIntegral
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (e : ℂ)
    (γ : Path (Real.pi : ℂ) e) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγΩ : ∀ t : unitInterval, γ t ∈ Ω)
    (hsin : ∀ t ∈ Ioo (0 : ℝ) 1, Complex.sin (γ.extend t) ≠ 0)
    (Q : ℂ × CoeffPair p → ℂ)
    (hroot : ∀ t ∈ Ioo (0 : ℝ) 1,
      Q (sourceAngularBranchCosinePoint hp hp1 m δ (γ.extend t,ψ),ψ) =
        sourceAngularBranchCosineRoot hp hp1 m δ (γ.extend t,ψ)) :
    let η := γ.map (continuous_sourceAngularBranchCosinePoint_spectral hp hp1 m δ ψ)
    CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) η ∧
      sourceAngularPathIntegral m s Q ψ η = sourceAngularBranchEtaRepresentative hp hp1 m s δ (e,ψ) := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand m s Q (z,ψ)
  let g : ℂ → ℂ := fun θ => sourceAngularBranchCosineLiftedIntegrand hp hp1 m m s δ (θ,ψ)
  let T : ℂ → ℂ := fun θ => sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ)
  let dT : ℂ → ℂ := fun θ => -δ ψ * Complex.sin θ
  have hT : Continuous T := continuous_sourceAngularBranchCosinePoint_spectral hp hp1 m δ ψ
  have hpull : ∀ t ∈ Ioo (0 : ℝ) 1, f (T (γ.extend t)) * dT (γ.extend t) = g (γ.extend t) := by
    intro t ht
    dsimp only [f,g,T,dT,sourceAngularIntegrand,sourceAngularBranchCosineLiftedIntegrand]
    rw [hroot t ht]
  have htrans := holomorphicPathPullback_integral_and_integrability f g T dT hT γ hγ
    (fun t _ => hasDerivAt_sourceAngularBranchCosinePoint hp hp1 m δ ψ (γ.extend t)) hpull
  have hlift := D.etaRepresentative_eq_lifted_pathIntegral ψ hψ e γ hγ hγΩ hsin
  exact ⟨htrans.1.mpr hlift.1,htrans.2.trans hlift.2⟩

/-- The explicit eta model pulls back to the constant one-form, so its
integral is the terminal angle minus pi. Integrability is automatic. -/
theorem model_pathIntegral_eq_angle_sub_pi
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (e : ℂ)
    (γ : Path (Real.pi : ℂ) e) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγΩ : ∀ t : unitInterval, γ t ∈ Ω)
    (hsin : ∀ t ∈ Ioo (0 : ℝ) 1, Complex.sin (γ.extend t) ≠ 0)
    (Q : ℂ × CoeffPair p → ℂ)
    (hroot : ∀ t ∈ Ioo (0 : ℝ) 1,
      Q (sourceAngularBranchCosinePoint hp hp1 m δ (γ.extend t,ψ),ψ) =
        sourceAngularBranchCosineRoot hp hp1 m δ (γ.extend t,ψ)) :
    let η := γ.map (continuous_sourceAngularBranchCosinePoint_spectral hp hp1 m δ ψ)
    CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) η ∧
      (∫ᶜ z in η, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q) z) =
        e - (Real.pi : ℂ) := by
  let f := sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q
  let g : ℂ → ℂ := fun _ => 1
  let T : ℂ → ℂ := fun θ => sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ)
  let dT : ℂ → ℂ := fun θ => -δ ψ * Complex.sin θ
  have hT : Continuous T := continuous_sourceAngularBranchCosinePoint_spectral hp hp1 m δ ψ
  have hpull : ∀ t ∈ Ioo (0 : ℝ) 1, f (T (γ.extend t)) * dT (γ.extend t) = g (γ.extend t) := by
    intro t ht
    have htΩ : γ.extend t ∈ Ω := by
      simpa only [Path.extend_apply γ (Ioo_subset_Icc_self ht)] using hγΩ ⟨t,Ioo_subset_Icc_self ht⟩
    have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ (T (γ.extend t)) m
      (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall (D.cosine_enclosed ψ hψ (γ.extend t) htΩ)))
    change sourceStandardRootOmittedProduct hp hp1 m ψ
      (sourceAngularBranchCosinePoint hp hp1 m δ (γ.extend t,ψ)) ≠ 0 at hP
    dsimp only [f,g,T,dT,sourceAngularEtaPathModelIntegrand]
    rw [hroot t ht]
    dsimp only [sourceAngularBranchCosineRoot]
    field_simp [D.halfGap_ne_zero ψ hψ,hP,hsin t ht]
  have htrans := holomorphicPathPullback_integral_and_integrability f g T dT hT γ hγ
    (fun t _ => hasDerivAt_sourceAngularBranchCosinePoint hp hp1 m δ ψ (γ.extend t)) hpull
  have hg : ContinuousOn (holomorphicOneForm g) univ := by
    change ContinuousOn (fun _ : ℂ => (1 : ℂ) • ContinuousLinearMap.id ℂ ℂ) univ
    exact continuousOn_const
  have hint : CurveIntegrable (holomorphicOneForm g) γ :=
    hg.curveIntegrable_of_contDiffOn hγ (fun _ => mem_univ _)
  have heval : (∫ᶜ θ in γ, holomorphicOneForm g θ) = e - (Real.pi : ℂ) :=
    curveIntegral_eq_sub_of_primitive g (fun θ => θ) univ (fun θ _ => hasDerivAt_id θ)
      γ hγ (fun _ _ => mem_univ _) hint
  exact ⟨htrans.1.mpr hint,htrans.2.trans heval⟩

end SourceAngularBranchCosineChartData
end NLS.ZakharovShabat
