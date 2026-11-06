import NLS.KdV.HillHminusRelativeAction
import NLS.KdV.HillFixedPhysicalAction
import NLS.KdV.HillLocalPhysicalRootMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- Every relative H-minus-one action is the original physical action on
an actual L2 neighborhood of its reference, including a collapsed gap. -/
theorem exists_hillHminusRelativeAction_original_matching
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ q ∈ V ∧
      ∀ p ∈ V, hillHminusRelativeAction q.val q.property.1 q.property.2 n
          (hillOriginalHminusSource p.val) =
        (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ) := by
  obtain ⟨V,hV,hqV,hroots⟩ := exists_hillAbelianComplexRoot_physical_contour_neighborhood
    q.val q.property.1 q.property.2 n hn
  obtain ⟨W,hW,hqW,hgeom⟩ := exists_hillIntrinsicContour_local_physical_geometry
    q.val q.property.1 q.property.2 n hn
  refine ⟨V ∩ W,hV.inter hW,⟨hqV,hqW⟩,?_⟩
  intro p hp
  let c := hillRealGapCenter q.val q.property.1 q.property.2 n
  let R := hillRealGapHalfLength q.val q.property.1 q.property.2 n +
    hillRealGapCollar q.val q.property.1 q.property.2 n
  have hR : 0 ≤ R := add_nonneg
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 n hn).1
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 n hn).2.1.le
  have hd : hillHminusDiscriminant (hillOriginalHminusSource p.val) =
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) := by
    funext z
    exact hillHminusDiscriminant_original_source_agreement p.val p.property.1 z
  have he : hillHminusRelativeAction q.val q.property.1 q.property.2 n
        (hillOriginalHminusSource p.val) =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((c : ℂ),R),
        z * deriv (hillL2Discriminant (SpectralWeight.one.toCoeff p.val)) z /
          hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 z := by
    unfold hillHminusRelativeAction
    congr 1
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only [hillHminusRelativeActionIntegrand]
    rw [hd,hillHminusRelativeRoot_original_source _ _ _ p.val p.property.1,
      (hroots p hp.1 z hz).2.2]
  rw [he]
  exact hillFixedContourAction_eq_gapIntegral p.val p.property.1 p.property.2 n hn c R hR
    (hgeom p hp.2).1 (hgeom p hp.2).2

theorem hillHminusRelativeAction_base
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    hillHminusRelativeAction q.val q.property.1 q.property.2 n
        (hillOriginalHminusSource q.val) =
      (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ) := by
  obtain ⟨V,_,hq,hmatch⟩ := exists_hillHminusRelativeAction_original_matching q n hn
  exact hmatch q hq

end NLS.KdV
