import NLS.Articles.KdVKdV2Frequencies.GlobalNativeRealInverse

/-! # Global real analytic diffeomorphisms at ALL native Sobolev orders

Every native inverse is the literal restriction of the ONE already-fixed
weak global inverse. Existing matched complex inverse charts identify its
native analytic germs at EVERY target. Both native norms, both inverse
identities, the global inclusion diagrams and FULL signed recovery remain.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- At EVERY native target and EVERY order, a genuine OPEN complex
analytic germ equals the SAME restricted global inverse on its ENTIRE
real target slice. No independent native inverse is chosen. -/
theorem realNativeInverse_has_complex_germ (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (z : physicalRealDeletedSubmodule) :
    ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ z.val∈T ∧
      ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0, AnalyticOnNhd ℂ G T ∧
        ∀ y : physicalRealDeletedSubmodule, y.val∈T → G y.val=(D.realNativeInverse t ht y).val := by
  let a := D.realNativeInverse t ht z
  let c := physicalRealSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a
  have hcr := (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) c.val).mpr c.property
  obtain ⟨P0,hP0,hc,_hsub,_hP0a,hP0ia,hreal0,_hraw0⟩ := D.exists_real_weak_analytic_inverse_at c.val hcr
  obtain ⟨V,_hV,haV,g,_hga,hcomm,P,hP,_haP,_hPV,_hFa,hPia,T,hT,hbase,hTP,hmatch⟩ :=
    D.native_inverse_matches_weak_chart P0 hP0 hP0ia t ht a.val (realNativeSource_real t ht a) hc
  have hPa : P a.val=(D.realNativeForward t ht a).val := by
    rw [hP]
    apply WeightedCoeff.meanZeroSobolevInclusion_injective (by linarith : (-1/2 : ℝ)≤t-1/2)
    have h := nativeMeanZeroAbelianMap_commuting t ht D.signed g a.val (hcomm _ haV).2.1
    exact h.trans (congrArg Subtype.val (D.realNativeForward_weak_commuting t ht a)).symm
  have hPz : P a.val=z.val := hPa.trans (congrArg Subtype.val (D.realNativeForward_inverse t ht z))
  refine ⟨T,hT,hPz ▸ hbase,P.symm,hPia.mono hTP,?_⟩
  intro y hy
  have h := hmatch y.val hy
  have hw := D.weak_chart_inverse_eq_global P0 hP0 hreal0
    (physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) y) h.1
  apply WeightedCoeff.meanZeroSobolevInclusion_injective (by linarith : (-1 : ℝ)≤t-1)
  exact h.2.1.trans (hw.trans (congrArg Subtype.val (D.realNativeInverse_weak_commuting t ht y)).symm)

/-- Analyticity of the SAME global inverse in EVERY native source and
target Banach norm, including EVERY order s=t-1>=-1. -/
theorem realNativeInverse_analytic (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    AnalyticOnNhd ℝ (D.realNativeInverse t ht) univ := by
  intro z _
  obtain ⟨T,hT,hz,G,hG,hmatch⟩ := D.realNativeInverse_has_complex_germ t ht z
  apply (analyticAt_physicalRealDeletedRestriction (hG z.val hz)).congr
  filter_upwards [(hT.preimage continuous_subtype_val).mem_nhds hz] with y hy
  change physicalRealDeletedProjection (G y.val)=D.realNativeInverse t ht y
  rw [hmatch y hy]
  exact physicalRealDeletedProjection_coe _

/-- The actual global real analytic native diffeomorphism. The inverse
function is EXPLICITLY the restriction of the already-fixed weak inverse. -/
def realNativeHomeomorph (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    physicalRealDeletedSubmodule ≃ₜ physicalRealDeletedSubmodule where
  toEquiv := D.realNativeEquiv t ht
  continuous_toFun := (D.realNativeForward_analytic t ht).continuous
  continuous_invFun := (D.realNativeInverse_analytic t ht).continuous

@[simp] theorem realNativeHomeomorph_apply (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    D.realNativeHomeomorph t ht a=D.realNativeForward t ht a := rfl

@[simp] theorem realNativeHomeomorph_symm_apply (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (z : physicalRealDeletedSubmodule) :
    (D.realNativeHomeomorph t ht).symm z=D.realNativeInverse t ht z := rfl

/-- ONE global real rough inverse is fixed BEFORE ALL native orders.
Every order has the ACTUAL global real analytic diffeomorphism with exact
weak compatibility and FULL original signed native target recovery. -/
theorem exists_one_global_weak_inverse_all_native_diffeomorphisms (D : GlobalRoughAbelianForwardData) :
    ∃ e0 : physicalRealDeletedSubmodule ≃ₜ physicalRealDeletedSubmodule,
      (∀ a, e0 a=D.realWeakForward a) ∧
      AnalyticOnNhd ℝ (fun a => e0 a) univ ∧ AnalyticOnNhd ℝ e0.symm univ ∧
      ∀ (t : ℝ) (ht : 0≤t),
        ∃ e : physicalRealDeletedSubmodule ≃ₜ physicalRealDeletedSubmodule,
          (∀ a, e a=D.realNativeForward t ht a) ∧
          AnalyticOnNhd ℝ (fun a => e a) univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
          (∀ z, physicalRealSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) (e.symm z)=
            e0.symm (physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) z)) ∧
          ∀ z, D.signed (realNativeSource t ht (e.symm z))=
            WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z.val) := by
  refine ⟨D.realWeakHomeomorph,fun _ => rfl,D.realWeakForward_analytic,D.realWeakEquiv_symm_analytic,?_⟩
  intro t ht
  exact ⟨D.realNativeHomeomorph t ht,fun _ => rfl,D.realNativeForward_analytic t ht,
    D.realNativeInverse_analytic t ht,D.realNativeInverse_weak_commuting t ht,D.realNativeInverse_full_signed_recovery t ht⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
