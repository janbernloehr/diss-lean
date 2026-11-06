import NLS.Articles.KdVConvexity.MainTheorem12Forward
import NLS.KdV.HillRoughFourierLebesgueInverseAllExponents

/-! # Theorem 1.2: the actual global native real analytic diffeomorphism

For every -1/2 <= s <= 0 and every finite p >= 2, the SAME physical
Birkhoff map and its already-fixed global inverse are real analytic in
both original Fourier-Lebesgue norms. All signed Fourier coefficients,
zero mean, Fourier reality, and the fixed weak inclusion diagrams agree.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

/-- All native analytic requirements of the source Theorem 1.2 are
proved for ONE actual physical map before every regularity and exponent. -/
theorem theorem_1_2 : Nonempty Theorem12PhysicalData := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  refine ⟨⟨D,?_,?_⟩⟩
  · intro s hs _hupper p hp h2p inst
    exact D.fourierLebesgueForward_analytic s hs p hp h2p
  · intro s hs _hupper p hp h2p inst
    exact D.fourierLebesgueEquiv_symm_analytic s hs p hp h2p

/-- The full global real analytic bijection in its original native
norms, with BOTH fixed weak diagrams and every signed inverse coefficient. -/
theorem theorem_1_2_global_native_analytic_diffeomorphism :
    ∃ D : GlobalRoughAbelianForwardData,
      ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
      ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      ∃ e : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p ≃
          physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p,
        AnalyticOnNhd ℝ (fun a => e a) univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
        (∀ a, e a=D.fourierLebesgueForward s hs p hp h2p a) ∧
        (∀ a, fourierLebesgueTargetNormalization s hs p hp h2p (e a)=
          D.realWeakHomeomorph (fourierLebesgueSourceNormalization s hs p hp h2p a)) ∧
        (∀ z, fourierLebesgueSourceNormalization s hs p hp h2p (e.symm z)=
          D.realWeakHomeomorph.symm (fourierLebesgueTargetNormalization s hs p hp h2p z)) ∧
        (∀ z, D.signed (fourierLebesgueSourceInclusion s hs p hp h2p (e.symm z).val)=
          fourierLebesgueTargetInclusion s hs p hp h2p z.val) := by
  obtain ⟨T⟩ := theorem_1_2
  refine ⟨T.physicalMap,?_⟩
  intro s hs hupper p hp h2p inst
  exact ⟨T.physicalMap.fourierLebesgueEquiv s hs p hp h2p,
    T.analytic_forward s hs hupper p hp h2p,T.analytic_inverse s hs hupper p hp h2p,
    (fun _ => rfl),T.physicalMap.fourierLebesgueForward_weak_commuting s hs p hp h2p,
    T.physicalMap.fourierLebesgueEquiv_symm_weak_commuting s hs p hp h2p,
    T.physicalMap.fourierLebesgueEquiv_symm_signed s hs p hp h2p⟩

end NLS.Articles.KdVConvexity
