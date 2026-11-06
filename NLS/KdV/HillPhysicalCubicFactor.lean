import NLS.KdV.HillL2CubicPhysicalPeriods
import NLS.ComplexAnalysis.QuadraticGapCubicFactor

/-! # The literal physical cubic period has its exact fourth-gap factor -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2RealCubicContourMoment_eq_root_factor
    {A : Type} (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (Q : ℂ × A → ℂ) (s : A → ℂ) (a : A)
    (hs : (hillRealGapHalfLength q hq hr n : ℂ)^2=s a)
    (R : ℝ) (hdR : hillRealGapHalfLength q hq hr n < R)
    (hR : R ≤ hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    (hQ : AnalyticOnNhd ℂ (fun z => Q (z-(hillRealGapCenter q hq hr n : ℂ),a))
      (closedBall (hillRealGapCenter q hq hr n : ℂ) R))
    (hamp : ∀ z ∈ ball (hillRealGapCenter q hq hr n : ℂ) R \
        segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi =
        Q (z-(hillRealGapCenter q hq hr n : ℂ),a)*
          endpointRoot (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) z) :
    hillL2RealCubicContourMoment q hq hr n=
      (hillRealGapHalfLength q hq hr n : ℂ)^4*cubicRootAmplitudeFactor Q s a := by
  let τ := hillRealGapCenter q hq hr n
  let δ := hillRealGapHalfLength q hq hr n
  let η := hillRealGapCollar q hq hr n
  let r := (δ+R)/2
  let K := segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)
  let F : ℂ → ℂ := fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi
  obtain ⟨hd,hη,hl,hu,hsub⟩ := hillRealGapContour_geometry q hq hr n hn
  have hdr : δ < r := by dsimp only [r,δ];linarith
  have hrR : r < R := by dsimp only [r,δ];linarith
  have hrpos : 0 < r := hd.trans_lt hdr
  have hdδ : 0 ≤ δ := hd
  have hrδ : ‖(δ : ℂ)‖ < r := by
    rw [norm_real,Real.norm_eq_abs,abs_of_nonneg hdδ]
    exact hdr
  have hrcan : r ≤ δ+η := hrR.le.trans hR
  have hleft : (τ : ℂ)-(δ : ℂ)=(hillRealLabels q hq hr (2*n-1) : ℂ) := by rw [←ofReal_sub,hl]
  have hright : (τ : ℂ)+(δ : ℂ)=(hillRealLabels q hq hr (2*n) : ℂ) := by rw [←ofReal_add,hu]
  have hKsmall : K ⊆ ball (τ : ℂ) r := by
    rw [show K=segment ℝ ((τ : ℂ)-δ) ((τ : ℂ)+δ) by rw [hleft,hright]]
    exact (convex_ball (τ : ℂ) r).segment_subset
      (by simpa only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg] using hrδ)
      (by simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hrδ)
  have hF : AnalyticOnNhd ℂ (fun z => F z^3) (ball (τ : ℂ) (δ+2*η) \ K) :=
    (((analyticOnNhd_hillL2RealCutPrimitive q hq hr).mono hsub).add analyticOnNhd_const).pow 3
  have hdef := circleIntegral_eq_of_analytic_cut_nestedCircles (fun z => F z^3)
    (ball (τ : ℂ) (δ+2*η)) K hF (τ : ℂ) (τ : ℂ) r (δ+η) hrpos
    (add_pos_of_nonneg_of_pos hd hη) hKsmall
    (fun z hz => ball_subset_ball hrcan (hKsmall hz))
    (closedBall_subset_closedBall hrcan) (closedBall_subset_ball (by linarith))
  have hmatch : (∮ z in C((τ : ℂ),r), F z^3) =
      ∮ z in C((τ : ℂ),r), (Q (z-τ,a)*endpointRoot ((τ : ℂ)-δ) ((τ : ℂ)+δ) z)^3 := by
    apply circleIntegral.integral_congr hrpos.le
    intro z hz
    have hzK : z ∉ K := fun hk => sphere_disjoint_ball.le_bot ⟨hz,hKsmall hk⟩
    have he := hamp z ⟨closedBall_subset_ball hrR (sphere_subset_closedBall hz),hzK⟩
    simpa only [F,hleft,hright] using congrArg (fun x : ℂ => x^3) he
  have hi := cubicRootAmplitudeFactor_eq_shifted_root_period Q s a (τ : ℂ) (δ : ℂ) hs r R hrδ hrR hQ
  change (Real.pi : ℂ)⁻¹*(∮ z in C((τ : ℂ),δ+η), F z^3)=_
  rw [←hdef,hmatch]
  exact hi

end NLS.KdV
