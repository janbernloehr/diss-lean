import NLS.Articles.KdVConvexity.FourierLebesgueFiniteGapApproximation
import NLS.Articles.KdVConvexity.FourierLebesguePhaseCompatibility
import NLS.Articles.KdVConvexity.FourierLebesgueFrequencyRecovery
import NLS.Articles.KdVConvexity.WeakPhysicalPhaseEvolution

/-! # Theorem 1.3: the actual global continuous physical phase evolution

ONE physical map and ONE actual frequency family precede every order
and finite exponent in the source's precise range. Global group laws,
native continuity, weak normalization compatibility and native finite-gap
approximation uniform on compact times are proved unconditionally.

This is not yet Theorem 1.3. It remains to prove the literal KdV time-PDE
for the approximating smooth orbits, recover every classical smooth
solution, and then establish the universal smooth-approximation solution
notion of Kappeler--Topalov, Definition 1.1 (Duke Math. J. 135 (2006), p.328).
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

/-- All global topological and native approximation requirements are
proved for the ACTUAL physical phase evolution on the full article range.
Classical KdV PDE recovery and universal smooth-approximation uniqueness
remain explicit mathematical obligations, rather than hypotheses hidden
in this unconditional preparation theorem. -/
theorem theorem_1_3_global_continuous_phase_preparation :
    ∃ (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension),
      ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
      ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      let Φ := D.fourierLebesguePhaseEvolution B s hs p hp h2p
      Continuous (fun x : ℝ × physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p => Φ x.1 x.2) ∧
      (∀ q, Φ 0 q=q) ∧
      (∀ t u q, Φ t (Φ u q)=Φ (t+u) q) ∧
      (∀ t q, fourierLebesgueSourceNormalization s hs p hp h2p (Φ t q)=
        D.weakPhysicalPhaseEvolution B t (fourierLebesgueSourceNormalization s hs p hp h2p q)) ∧
      ∀ q,
        Tendsto (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q) atTop (𝓝 q) ∧
        (∀ N t, ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ ∀ n : ℤ,
          (Φ t (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N)).val.val n=
            periodOneCoefficient f n) ∧
        ∀ K : Set ℝ, IsCompact K →
          TendstoUniformlyOn (fun N t => Φ t (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N))
            (fun t => Φ t q) atTop K := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨B⟩ := nonempty_basePhysicalFrequencyExtension
  refine ⟨D,B,?_⟩
  intro s hs _hupper p hp h2p inst
  refine ⟨D.continuous_fourierLebesguePhaseEvolution B s hs p hp h2p,
    D.fourierLebesguePhaseEvolution_zero B s hs p hp h2p,
    D.fourierLebesguePhaseEvolution_add B s hs p hp h2p,
    D.fourierLebesguePhaseEvolution_weak_commuting B s hs p hp h2p,?_⟩
  intro q
  exact ⟨D.tendsto_fourierLebesgueFiniteGapApproximation s hs p hp h2p q,
    D.fourierLebesgueFiniteGapApproximation_orbit_smooth s hs p hp h2p B q,
    D.tendstoUniformlyOn_fourierLebesgueFiniteGapApproximation s hs p hp h2p B q⟩

end NLS.Articles.KdVConvexity
