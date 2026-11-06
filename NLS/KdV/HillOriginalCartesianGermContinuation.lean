import NLS.KdV.HillOriginalAllGapCartesianGardner
import NLS.KdV.HillRealSourceSubmodule
import Mathlib.Analysis.Analytic.Uniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The literal ORIGINAL signed Cartesian coordinate is real analytic
on the entire original real L2 source space. -/
theorem analyticOnNhd_hillSignedSpectralCartesian_real_submodule (n : ℕ+) (σ : Bool) :
    AnalyticOnNhd ℝ (fun p : hillRealSourceSubmodule =>
      hillSignedSpectralCartesian σ n ⟨p.val,p.property⟩) univ := by
  intro p _
  let q : RealPeriodOneHillPotential := ⟨p.val,p.property⟩
  obtain ⟨F,hF,hFM⟩ := exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps q n σ
  let L : hillRealSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    (hillOriginalHminusSource.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hA : AnalyticAt ℝ (fun r : hillRealSourceSubmodule => F (L r)) p :=
    (hF.restrictScalars (𝕜 := ℝ)).comp (f := L) (L.analyticAt p)
  have hQ : Continuous (fun r : hillRealSourceSubmodule =>
      (⟨r.val,r.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  exact hA.congr (hQ.continuousAt.tendsto.eventually hFM)

/-- ORIGINAL physical germ matching propagates to EVERY original real
source in the same analytic H-minus-one ball. Convexity and real-analytic
uniqueness remove the original L2-closeness restriction. -/
theorem hillSignedCartesian_hminus_physical_germ_matches_ball
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) (ε : ℝ) (hε : 0 < ε)
    (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticOnNhd ℂ F (ball (hillOriginalHminusSource q.val) ε))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p) :
    ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ ball (hillOriginalHminusSource q.val) ε →
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p := by
  let L : hillRealSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    (hillOriginalHminusSource.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  let V := L ⁻¹' ball (hillOriginalHminusSource q.val) ε
  let Q : hillRealSourceSubmodule := ⟨q.val,q.property⟩
  have hV : Convex ℝ V := (convex_ball (hillOriginalHminusSource q.val) ε).linear_preimage L.toLinearMap
  have hFA : AnalyticOnNhd ℝ (fun r : hillRealSourceSubmodule => F (L r)) V := by
    intro r hr
    exact ((hF _ hr).restrictScalars (𝕜 := ℝ)).comp (f := L) (L.analyticAt r)
  have hGA : AnalyticOnNhd ℝ (fun r : hillRealSourceSubmodule =>
      hillSignedSpectralCartesian σ n ⟨r.val,r.property⟩) V :=
    (analyticOnNhd_hillSignedSpectralCartesian_real_submodule n σ).mono (subset_univ _)
  have hQ : Continuous (fun r : hillRealSourceSubmodule =>
      (⟨r.val,r.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  have hnear : (fun r : hillRealSourceSubmodule => F (L r)) =ᶠ[𝓝 Q]
      (fun r => hillSignedSpectralCartesian σ n ⟨r.val,r.property⟩) :=
    hQ.continuousAt.tendsto.eventually hFM
  have hqV : Q ∈ V := by
    change hillOriginalHminusSource q.val ∈ ball (hillOriginalHminusSource q.val) ε
    exact mem_ball_self hε
  have hpre : IsPreconnected V := hV.isPreconnected
  have heq : EqOn (fun r : hillRealSourceSubmodule => F (L r))
      (fun r => hillSignedSpectralCartesian σ n ⟨r.val,r.property⟩) V :=
    hFA.eqOn_of_preconnected_of_eventuallyEq (z₀ := Q) hGA hpre hqV hnear
  intro p hp
  have hpV : (⟨p.val,p.property⟩ : hillRealSourceSubmodule) ∈ V := by
    change hillOriginalHminusSource p.val ∈ ball (hillOriginalHminusSource q.val) ε
    exact hp
  exact heq hpV

/-- BOTH literal ORIGINAL Cartesian signs have H-minus-one analytic
balls matching EVERY original real source in that ball, with no
isospectral or original L2-closeness assumption. -/
theorem exists_hillOriginal_signedCartesian_hminus_physical_ball
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ F (ball (hillOriginalHminusSource q.val) ε) ∧
      ∀ p : RealPeriodOneHillPotential,
        hillOriginalHminusSource p.val ∈ ball (hillOriginalHminusSource q.val) ε →
        F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p := by
  obtain ⟨F,hF,hFM⟩ := exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps q n σ
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ F) (hillOriginalHminusSource q.val) hF
  have hFB : AnalyticOnNhd ℂ F (ball (hillOriginalHminusSource q.val) ε) := fun a ha => hball ha
  exact ⟨ε,hε,F,hFB,hillSignedCartesian_hminus_physical_germ_matches_ball q n σ ε hε F hFB hFM⟩

/-- Every ORIGINAL signed Cartesian value is continuous along arbitrary
strong H-minus-one convergent sequences of original real potentials,
including closed gaps. No isospectral or L2-convergence hypothesis is used. -/
theorem hillSignedSpectralCartesian_tendsto_of_original_hminus
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) (p : ℕ → RealPeriodOneHillPotential)
    (hp : Tendsto (fun j => hillOriginalHminusSource (p j).val) atTop (𝓝 (hillOriginalHminusSource q.val))) :
    Tendsto (fun j => hillSignedSpectralCartesian σ n (p j)) atTop (𝓝 (hillSignedSpectralCartesian σ n q)) := by
  obtain ⟨ε,hε,F,hF,hM⟩ := exists_hillOriginal_signedCartesian_hminus_physical_ball q n σ
  have hq : hillOriginalHminusSource q.val ∈
      ball (hillOriginalHminusSource q.val) ε := mem_ball_self hε
  have hc := (hF _ hq).continuousAt.tendsto.comp hp
  rw [hM q hq] at hc
  apply hc.congr'
  filter_upwards [hp.eventually (isOpen_ball.mem_nhds hq)] with j hj
  exact hM (p j) hj

end NLS.KdV
