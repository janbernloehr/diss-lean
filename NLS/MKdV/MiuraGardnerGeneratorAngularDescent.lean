import NLS.MKdV.MiuraNativeActionFlowAllTimes
import NLS.MKdV.MiuraOppositeAngularCoordinateDescent

/-! # Actual negative Gardner generators give the global angular product factor

The hypothesis is an actual differential identity for an independently
specified H¹ functional with physical H¹ gradients. It prescribes neither
its values nor a factor through actions. The native chain rule integrates
that identity along the complete action flows; the full infinite action
fiber argument then proves the global product factorization.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem independent_functional_action_rotation_of_Gardner_generator
    (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (F : ScalarDomain 2 → ℂ)
    (P : ∀ a : MiuraRealSobolevSource s,
      SobolevGardnerGradientAt F (hierarchySobolevToScalarDomain s hs a.val))
    (hgen : ∀ a : MiuraRealSobolevSource s, ∀ n : ℕ, 1 ≤ n →
      reflectedHilbertPairing (scalarInclusion (P a).gradient)
        (l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)) =
          -(if m = n then I else 0)*F (hierarchySobolevToScalarDomain s hs a.val))
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    F (hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val) =
      Complex.exp (-(if m = n then I else 0)*(t : ℂ))*F (hierarchySobolevToScalarDomain s hs a.val) := by
  let f : ℝ → ℂ := fun r => F (hierarchySobolevToScalarDomain s hs
    (miuraNativeRealActionFlow s a n r).val)
  have hd (r : ℝ) : HasDerivAt f (-(if m = n then I else 0)*f r) r := by
    have h := hasDerivAt_independent_functional_miuraActionFlow_allTimes s hs a n hn r F
      (P (miuraNativeRealActionFlow s a n r))
    rw [hgen _ n hn] at h
    exact h
  have h := NLS.FunctionalAnalysis.eq_scalarExponential_of_hasDerivAt _ f hd t
  have hz : f 0 = F (hierarchySobolevToScalarDomain s hs a.val) := by
    change F (hierarchySobolevToScalarDomain s hs (miuraActionFlow s a.val (fun j => a.property j) n 0)) = _
    rw [miuraActionFlow_zero]
  exact h.trans (congrArg (fun q => Complex.exp (-(if m = n then I else 0)*(t : ℂ))*q) hz)

/-- Global action dependence of the actual NLS angular coordinate times
any independently specified H¹ angular functional with negative Gardner
unit generators. No action-dependence or angle values are assumed. -/
theorem exists_independent_Gardner_angular_product_action_factor
    (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (hm : 1 ≤ m) (F : ScalarDomain 2 → ℂ)
    (P : ∀ a : MiuraRealSobolevSource s,
      SobolevGardnerGradientAt F (hierarchySobolevToScalarDomain s hs a.val))
    (hgen : ∀ a : MiuraRealSobolevSource s, ∀ n : ℕ, 1 ≤ n →
      reflectedHilbertPairing (scalarInclusion (P a).gradient)
        (l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)) =
          -(if m = n then I else 0)*F (hierarchySobolevToScalarDomain s hs a.val)) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ, ∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) =
        miuraNativeNLSAngularCoordinate s m a*F (hierarchySobolevToScalarDomain s hs a.val) := by
  have hc : Continuous (fun a : MiuraRealSobolevSource s => F (hierarchySobolevToScalarDomain s hs a.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    have hH : Continuous (fun b : MiuraRealSobolevSource s => hierarchySobolevToScalarDomain s hs b.val) :=
      (hierarchySobolevToScalarDomain s hs).continuous.comp continuous_subtype_val
    exact (P a).hasFDerivAt.continuousAt.comp
      (f := fun b : MiuraRealSobolevSource s => hierarchySobolevToScalarDomain s hs b.val)
      (x := a) hH.continuousAt
  exact exists_opposite_angular_product_action_factor s hs m hm _ hc
    (fun a n hn t => independent_functional_action_rotation_of_Gardner_generator s hs m F P hgen a n hn t)

end NLS.MKdV
