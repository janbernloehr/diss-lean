import NLS.ZakharovShabat.SourceGapWeightedEta
import NLS.ZakharovShabat.SourceAngularEtaRemainderBound

/-! # Bounds for gap-weighted eta coordinates without gap division

The quadratic terminal identity controls the sine numerator by the
Dirichlet displacement and half the gap. A bound on the analytic eta
remainder therefore controls both signed coordinates, even at complex
collapsed gaps. Each fixed chart supplies a local bound automatically.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The terminal sine numerator is controlled without dividing by the gap. -/
theorem norm_sourceDirichletEtaSineNumerator_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    ‖sourceDirichletEtaSineNumerator hp hp1 n ψ‖ ≤
      ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
        sourceStandardRootMidpoint hp hp1 ψ n‖ + ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2 := by
  simpa only [sourceDirichletEtaSineNumerator,norm_div,norm_mul,norm_I,mul_one] using
    norm_sourceDirichletRootCoefficient_le hp hp1 ψ n hμ

/-- A single remainder bound controls both signs. The statement also
holds for any complex sign of norm at most one. -/
theorem norm_sourceGapWeightedEtaCoordinate_le_of_remainder_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (B : ℝ)
    (hB : ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ B) :
    ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤
      (4*Real.exp B) * (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
        ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
          sourceStandardRootMidpoint hp hp1 ψ n‖) := by
  let a := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
    sourceStandardRootMidpoint hp hp1 ψ n
  let b := sourceDirichletEtaSineNumerator hp hp1 n ψ
  let H := sourceAngularEtaRemainder hp hp1 n s ψ
  have hb := norm_sourceDirichletEtaSineNumerator_le hp hp1 n ψ hμ
  have hsb : ‖σ*I*b‖ ≤ ‖b‖ := by
    simpa only [norm_mul,norm_I,mul_one,one_mul] using
      mul_le_mul_of_nonneg_right hσ (norm_nonneg b)
  have hsum : 2*‖a+σ*I*b‖ ≤ 4*(‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+‖a‖) := by
    have ht := norm_add_le a (σ*I*b)
    change ‖b‖ ≤ ‖a‖+_ at hb
    nlinarith [norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n)]
  have hSH : ‖σ*I*H‖ ≤ B := by
    rw [norm_mul,norm_mul,norm_I,mul_one]
    exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg H)).trans (by simpa using hB)
  have he : ‖Complex.exp (σ*I*H)‖ ≤ Real.exp B :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hSH)
  change ‖-2*(a+σ*I*b)*Complex.exp (σ*I*H)‖ ≤ _
  rw [norm_mul,norm_mul,norm_neg,Complex.norm_ofNat]
  calc
    _ ≤ (4*(‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+‖a‖))*Real.exp B :=
      mul_le_mul hsum he (norm_nonneg _) (by positivity)
    _ = _ := by ring

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- At each point of an actual chart, one neighborhood and constant
control both signs. This includes every complex collapsed gap in the chart. -/
theorem exists_local_gapWeightedEtaCoordinate_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) V)
    (φ : CoeffPair p) (hφ : φ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
              sourceStandardRootMidpoint hp hp1 ψ n‖) := by
  let B := ‖sourceAngularEtaRemainder hp hp1 n s φ‖+1
  have hcont := (D.analyticOnNhd_etaRemainder ρ hrρ hρR hμ φ hφ).continuousAt.norm
  have hevent : ∀ᶠ ψ in 𝓝 φ, ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ < B :=
    hcont.eventually (gt_mem_nhds (by dsimp only [B]; linarith))
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hevent
  refine ⟨U ∩ V,hU.inter D.source_open,⟨hφU,hφ⟩,inter_subset_right,
    4*Real.exp B,by positivity,?_⟩
  intro ψ hψ σ hσ
  exact norm_sourceGapWeightedEtaCoordinate_le_of_remainder_bound hp hp1 n s ψ
    (((D.disc_family ψ hψ.2).contour_family.2 n).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ.2).dirichlet_mem_ball n)))
    σ hσ B (hUsub hψ.1).le

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
