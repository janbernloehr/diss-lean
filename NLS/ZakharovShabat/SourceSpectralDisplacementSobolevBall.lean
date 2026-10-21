import NLS.ZakharovShabat.SourceSpectralDisplacementCompact
import NLS.ZakharovShabat.SourceHigherSobolevBallCompact

/-! # Canonical displacement bounds on real Sobolev balls

Both boundary displacements and the critical displacement have common norm and inverse-index bounds over every real Hs ball.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both boundary displacements and the critical displacement have common
norm and inverse-index bounds on each entire real original Hs ball,
for every positive integer source order. -/
theorem exists_uniform_real_higherSobolev_displacement_envelopes
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D M : ℝ, 0 ≤ D ∧ 0 ≤ M ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      (∀ θ : BoundaryCondition,
        ‖sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab.val)‖ ≤ D ∧
        ∀ n : ℤ, (1+|(n:ℝ)|)*
          ‖sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab.val) n‖ ≤ M) ∧
      ‖sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab.val)‖ ≤ D ∧
      ∀ n : ℤ, (1+|(n:ℝ)|)*
        ‖sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab.val) n‖ ≤ M := by
  let J := higherSobolevSourceInclusion s
  let X := closedBall (0 : SobolevSource s) R ∩ (J ⁻¹' realTypeSourceLocus 2)
  let K := closure (J '' X)
  obtain ⟨hK,hKreal⟩ := higherSobolev_real_ball_image_compact s hs R
  obtain ⟨D,M,hD,hM,hbound⟩ := exists_source_all_displacement_envelopes_on_compact K hK hKreal
    (2*R) (by positivity)
  refine ⟨D,M,hD,hM,?_⟩
  intro ab hab
  have hmem : J ab.val ∈ K := subset_closure ⟨ab.val,⟨by simpa only [mem_closedBall,dist_zero_right] using hab,ab.property⟩,rfl⟩
  exact hbound (J ab.val) hmem (higherSobolevOperatorDomain s hs ab.val)
    ((norm_higherSobolevOperatorDomain_le s hs ab.val).trans (by gcongr))
    (higherSobolevOperatorDomain_compatibility s hs ab.val)

end NLS.ZakharovShabat
