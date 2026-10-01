import NLS.ZakharovShabat.WeightedResonantDiagonalCenter
import NLS.ComplexAnalysis.AnalyticImplicitRoot

/-!
# Analytic diagonal centers and tail-closing equations

The contraction comparison proves continuity of the named centers in
the source. Their nonzero residual derivative then makes them analytic
by the proved Banach implicit-root theorem. Evaluating the actual
off-diagonal entries at these moving centers gives analytic scalar
equations on one neighborhood for every distant index.
-/

noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual centers are analytic on any open source domain with
the common distant-strip analytic and diagonal bounds. -/
theorem analyticOnNhd_weightedResonantDiagonalCenter
    (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (U : Set (WeightedCoeffPair w.toWeight p)) (hU : IsOpen U)
    (hdom : U ×ˢ resonantStrip n ⊆ weightedCorrectionDomain hp w n)
    (hbound : ∀ ψ ∈ U, ∀ z ∈ resonantStrip n,
      ‖weightedResonantAExtension hp w ψ n z‖ ≤ Real.pi/32) :
    AnalyticOnNhd ℂ (fun ψ => weightedResonantDiagonalCenter hp w ψ n) U := by
  let a := fun ψ => weightedResonantDiagonalCenter hp w ψ n
  have ha (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ U) :
      AnalyticOnNhd ℂ (weightedResonantAExtension hp w ψ n) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_weightedResonantAExtension hp w n (ψ,z) (hdom ⟨hψ,hz⟩)).comp
      (analyticAt_const.prod analyticAt_id)
  have hdata (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ U) :=
    weightedResonantDiagonalCenter_spec hp w ψ n (ha ψ hψ) (hbound ψ hψ)
  intro ψ hψ
  have hζ : a ψ ∈ resonantStrip n := refinedResonantDisk_subset_strip n (hdata ψ hψ).1
  have hfixed : AnalyticAt ℂ
      (fun χ => weightedResonantAExtension hp w χ n (a ψ)) ψ :=
    (analyticAt_weightedResonantAExtension hp w n (ψ,a ψ) (hdom ⟨hψ,hζ⟩)).comp
      (f := fun χ : WeightedCoeffPair w.toWeight p => (χ,a ψ))
      (analyticAt_id.prod analyticAt_const)
  have herror : ContinuousAt (fun χ => (8/7 : ℝ)*
      ‖weightedResonantAExtension hp w χ n (a ψ)-weightedResonantAExtension hp w ψ n (a ψ)‖) ψ :=
    (hfixed.continuousAt.sub continuousAt_const).norm.const_mul _
  have hcont : ContinuousAt a ψ := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hnear : ∀ᶠ χ in 𝓝 ψ, (8/7 : ℝ)*
        ‖weightedResonantAExtension hp w χ n (a ψ)-weightedResonantAExtension hp w ψ n (a ψ)‖ < ε :=
      herror.eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [hU.mem_nhds hψ,hnear] with χ hχ hsmall
    rw [dist_eq_norm]
    exact (norm_resonantDiagonalCenters_sub_le n _ _ (ha χ hχ) (hbound χ hχ)
      (a χ) (a ψ) (hdata χ hχ).1 (hdata ψ hψ).1
      (hdata χ hχ).2.2.1 (hdata ψ hψ).2.2.1).trans_lt hsmall
  let F : ℂ × WeightedCoeffPair w.toWeight p → ℂ := fun t =>
    t.1-(Real.pi : ℂ)*n-weightedResonantAExtension hp w t.2 n t.1
  have hswap : AnalyticAt ℂ
      (fun t : ℂ × WeightedCoeffPair w.toWeight p => (t.2,t.1)) (a ψ,ψ) :=
    analyticAt_snd.prod analyticAt_fst
  have hAjoint : AnalyticAt ℂ
      (fun t : ℂ × WeightedCoeffPair w.toWeight p =>
        weightedResonantAExtension hp w t.2 n t.1) (a ψ,ψ) :=
    AnalyticAt.comp
      (g := fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantAExtension hp w t.1 n t.2)
      (f := fun t : ℂ × WeightedCoeffPair w.toWeight p => (t.2,t.1))
      (analyticAt_weightedResonantAExtension hp w n (ψ,a ψ) (hdom ⟨hψ,hζ⟩)) hswap
  have hF : AnalyticAt ℂ F (a ψ,ψ) :=
    (analyticAt_fst.sub analyticAt_const).sub hAjoint
  have hroot : ∀ᶠ χ in 𝓝 ψ, F (a χ,χ) = 0 := by
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    change a χ-(Real.pi : ℂ)*n-weightedResonantAExtension hp w χ n (a χ) = 0
    rw [sub_sub]
    exact sub_eq_zero.mpr (hdata χ hχ).2.2.1
  have hsection := deriv_spectral_section_eq_fderiv F (a ψ) ψ hF.differentiableAt
  have hsimple : (fderiv ℂ F (a ψ,ψ)) (1,0) ≠ 0 := by
    rw [← hsection]
    exact deriv_resonantDiagonalResidual_ne_zero n _ (ha ψ hψ) (hbound ψ hψ)
      (a ψ) (hdata ψ hψ).1
  exact analyticAt_implicitRoot F a ψ hF hcont hroot hsimple

/-- The centers and both actual tail-closing equations are analytic
on one open convex neighborhood for all distant signed indices. -/
theorem exists_uniform_analytic_weightedResonantCenterEquations
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => weightedResonantDiagonalCenter hp w ψ n) U ∧
        AnalyticOnNhd ℂ (fun ψ => weightedResonantBPlusExtension hp w ψ n
          (weightedResonantDiagonalCenter hp w ψ n)) U ∧
        AnalyticOnNhd ℂ (fun ψ => weightedResonantBMinusExtension hp w ψ n
          (weightedResonantDiagonalCenter hp w ψ n)) U := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hcontrol⟩ := exists_uniform_resonantDeterminant_control hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro n hn
  have hdom := (hcontrol n hn).1
  have hbound (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ U) (z : ℂ) (hz : z ∈ resonantStrip n) :=
    ((hcontrol n hn).2 ψ hψ z hz).2.1
  have ha := analyticOnNhd_weightedResonantDiagonalCenter hp w n U ho hdom hbound
  have hcenter (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ U) :
      weightedResonantDiagonalCenter hp w ψ n ∈ resonantStrip n := by
    apply refinedResonantDisk_subset_strip n
    apply (weightedResonantDiagonalCenter_spec hp w ψ n ?_ (hbound ψ hψ)).1
    intro z hz
    exact (analyticAt_weightedResonantAExtension hp w n (ψ,z) (hdom ⟨hψ,hz⟩)).comp
      (analyticAt_const.prod analyticAt_id)
  refine ⟨ha,?_,?_⟩
  · intro ψ hψ
    exact (analyticAt_weightedResonantBPlusExtension hp w n
      (ψ,weightedResonantDiagonalCenter hp w ψ n) (hdom ⟨hψ,hcenter ψ hψ⟩)).comp
      (f := fun χ : WeightedCoeffPair w.toWeight p => (χ,weightedResonantDiagonalCenter hp w χ n))
      (analyticAt_id.prod (ha ψ hψ))
  · intro ψ hψ
    exact (analyticAt_weightedResonantBMinusExtension hp w n
      (ψ,weightedResonantDiagonalCenter hp w ψ n) (hdom ⟨hψ,hcenter ψ hψ⟩)).comp
      (f := fun χ : WeightedCoeffPair w.toWeight p => (χ,weightedResonantDiagonalCenter hp w χ n))
      (analyticAt_id.prod (ha ψ hψ))

end NLS.ZakharovShabat
