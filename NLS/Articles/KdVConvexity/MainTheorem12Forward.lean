import NLS.Articles.KdVConvexity.MainTheorem12Preparation
import NLS.KdV.HillRoughFourierLebesgueForwardAllExponents

/-! # Theorem 1.2: native real analytic forward map and global fixed inverse

The SAME original physical restriction is a global bijection and is real
analytic in both original native source and target norms, for EVERY
-1/2<=s<=0 and finite p>=2. The inverse remains exactly the restriction
of the already-fixed rough inverse. Native inverse analyticity remains
an unproved field of `Theorem12PhysicalData`.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

/-- Unconditional native forward analyticity, global stronger bijection
and exact fixed inverse, on the full range of Theorem 1.2. -/
theorem theorem_1_2_native_forward_analytic :
    ∃ D : GlobalRoughAbelianForwardData,
      ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
      ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      ∃ e : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p ≃
          physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p,
        AnalyticOnNhd ℝ (fun a => e a) univ ∧
        (∀ a, e a=D.fourierLebesgueForward s hs p hp h2p a) ∧
        (∀ z, fourierLebesgueSourceNormalization s hs p hp h2p (e.symm z)=
          D.realWeakHomeomorph.symm (fourierLebesgueTargetNormalization s hs p hp h2p z)) ∧
        (∀ z, D.signed (fourierLebesgueSourceInclusion s hs p hp h2p (e.symm z).val)=
          fourierLebesgueTargetInclusion s hs p hp h2p z.val) := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  refine ⟨D,?_⟩
  intro s hs _hsupper p hp h2p inst
  exact ⟨D.fourierLebesgueEquiv s hs p hp h2p,D.fourierLebesgueForward_analytic s hs p hp h2p,
    (fun _ => rfl),D.fourierLebesgueEquiv_symm_weak_commuting s hs p hp h2p,
    D.fourierLebesgueEquiv_symm_signed s hs p hp h2p⟩

end NLS.Articles.KdVConvexity
