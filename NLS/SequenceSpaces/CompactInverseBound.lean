import NLS.SequenceSpaces.UniformInverseBound
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform inverse bounds over compact parameter sets

A family of bounded operators continuous in the operator norm and
invertible at every point of a compact parameter set has uniformly
bounded inverses. No continuity of the inverse family is assumed:
the local bound follows from the quantitative perturbation estimate.
-/

noncomputable section
open Set Topology

namespace NLS

/-- Operator-norm continuity and pointwise two-sided inverses on a
compact parameter set give one bound for all inverse norms. -/
theorem exists_uniform_inverse_norm_on_compact
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Set X) (hK : IsCompact K)
    (Q R : K → E →L[ℂ] E)
    (hQ : Continuous Q)
    (hQR : ∀ x : K, (Q x).comp (R x) =
      ContinuousLinearMap.id ℂ E)
    (hRQ : ∀ x : K, (R x).comp (Q x) =
      ContinuousLinearMap.id ℂ E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : K, ‖R x‖ ≤ M := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hlocal (x : K) : ∃ t ∈ 𝓝 x,
      Bornology.IsBounded (R '' t) := by
    let δ : ℝ := 1 / (2 * (‖R x‖ + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let t : Set K := {y | ‖Q y - Q x‖ < δ}
    have hcont : Continuous (fun y : K => ‖Q y - Q x‖) :=
      (hQ.sub continuous_const).norm
    have hopen : IsOpen t := isOpen_Iio.preimage hcont
    have hx : x ∈ t := by
      change ‖Q x - Q x‖ < δ
      simpa using hδ
    refine ⟨t,hopen.mem_nhds hx,?_⟩
    apply (isBounded_iff_forall_norm_le).2
    refine ⟨2 * ‖R x‖,?_⟩
    intro S hS
    obtain ⟨y,hy,rfl⟩ := hS
    change ‖Q y - Q x‖ < δ at hy
    have hdiff : ‖Q x - Q y‖ ≤ δ := by
      simpa only [norm_sub_rev] using (le_of_lt hy)
    have hnear : ‖R x‖ * ‖Q x - Q y‖ ≤ (1 / 2 : ℝ) := by
      calc
        ‖R x‖ * ‖Q x - Q y‖ ≤ ‖R x‖ * δ :=
          mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
        _ ≤ (‖R x‖ + 1) * δ := by
          gcongr
          linarith [norm_nonneg (R x)]
        _ = 1 / 2 := by
          dsimp [δ]
          have hpos : ‖R x‖ + 1 ≠ (0 : ℝ) := by positivity
          field_simp
    exact inverse_norm_le_two_mul_of_near
      (Q y) (Q x) (R y) (R x) (hQR y) (hRQ x) hnear
  have hbounded : Bornology.IsBounded (R '' (univ : Set K)) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
      isCompact_univ hlocal
  obtain ⟨M,hM⟩ := hbounded.exists_norm_le
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro x
  exact (hM (R x) ⟨x,mem_univ _,rfl⟩).trans (le_max_right _ _)

end NLS
