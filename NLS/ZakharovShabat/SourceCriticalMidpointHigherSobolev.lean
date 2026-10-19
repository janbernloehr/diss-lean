import NLS.SequenceSpaces.SobolevSquaredSymbol
import NLS.ZakharovShabat.SourceHmGapBounds
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform

/-! # Sobolev bounds for the actual critical-midpoint offset

The exact squared-gap identity gives a locally uniform H^(2s) bound, including central and collapsed gaps.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual critical point minus the periodic midpoint has twice the
source's Sobolev order, locally uniformly on complex Hs neighborhoods
of real sources. The formula includes central and collapsed gaps. -/
theorem exists_local_higherSobolev_critical_midpoint_bound
    (s : ℕ) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U, ∃ e : ScalarSobolev (2*s),
        (∀ n, e.val n =
          canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n-
          canonicalPeriodicMidpoint (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n) ∧
        ‖e‖ ≤ C := by
  let J := higherSobolevSourceInclusion s
  obtain ⟨Vg,hVg,haVg,R,hR,hgap⟩ := exists_local_sourceWeightedGapSequence_bound
    (by norm_num) (by norm_num) (SpectralWeight.sobolev s (Nat.cast_nonneg s))
    J (higherSobolevSourceWeightedPeriodOne s)
    (weightedBaseToPair_higherSobolevSourceWeightedPeriodOne s) a₀.val
  obtain ⟨Vq,hVq,haVq,B,hB,hquot⟩ := exists_local_uniform_sourceCriticalGapQuotient
    (by norm_num) (by norm_num) (J a₀.val) a₀.property
  refine ⟨Vg ∩ J ⁻¹' Vq,hVg.inter (hVq.preimage J.continuous),⟨haVg,haVq⟩,
    R^2*B,by positivity,?_⟩
  intro ab hab
  let g := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (J ab)
  let q := sourceCriticalGapQuotient (by norm_num) (by norm_num) (J ab)
  have hg (n : ℤ) : (1+|(n:ℝ)|)^s*‖g n‖ ≤ R :=
    (sourceHmWeightedGapSequence_majorant s ab n).trans
      ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ n).trans (hgap ab hab.1))
  obtain ⟨e,he,hen⟩ := WeightedCoeff.exists_sobolev_square_mul s (fun n => g n) q R hg
  refine ⟨e,?_,hen.trans (mul_le_mul_of_nonneg_left (hquot (J ab) hab.2).1 (sq_nonneg R))⟩
  intro n
  rw [he]
  exact ((hquot (J ab) hab.2).2 n).symm

end NLS.ZakharovShabat
