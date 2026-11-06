import NLS.Articles.KdVKdV2Frequencies.GlobalNativeRealDiffeomorphisms
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # Actual raw Sobolev real analytic Birkhoff diffeomorphisms

Explicit real linear isometries transport the verified normalized global
maps to the ACTUAL raw real mean-zero Sobolev source and target spaces.
Both analytic directions use the original native norms, and full signed
recovery identifies these maps with the SAME original global rough map.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

private theorem analytic_real_isometry_transport
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : E →L[ℝ] F) (L : G →L[ℝ] H) (f : F → G) (a : E)
    (hf : AnalyticAt ℝ f (J a)) : AnalyticAt ℝ (fun b => L (f (J b))) a := by
  exact (L.analyticAt _).comp (f := fun b => f (J b))
    (hf.comp (J.analyticAt a))

/-- The actual raw H^(t-1) to h^(t-1/2) global real homeomorphism, in
its ORIGINAL weighted norms and with the SAME weak global inverse. -/
def rawNativeHomeomorph (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1)) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1/2)) :=
  ((physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1))).symm.toHomeomorph.trans
    (D.realNativeHomeomorph t ht)).trans
      (physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1/2))).toHomeomorph

/-- Real analyticity in the ACTUAL raw native source AND target norms. -/
theorem rawNativeHomeomorph_analytic (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    AnalyticOnNhd ℝ (fun q => D.rawNativeHomeomorph t ht q) univ := by
  intro q _
  let es := physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1))
  let et := physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1/2))
  simpa only [rawNativeHomeomorph, realNativeHomeomorph, realNativeEquiv] using!
    analytic_real_isometry_transport
    (E := physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1)))
    (F := physicalRealDeletedSubmodule) (G := physicalRealDeletedSubmodule)
    (H := physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1/2)))
    es.symm.toContinuousLinearEquiv.toContinuousLinearMap et.toContinuousLinearEquiv.toContinuousLinearMap (D.realNativeForward t ht) q (D.realNativeForward_analytic t ht (es.symm q) (mem_univ _))

/-- The actual raw inverse is real analytic in the ORIGINAL native
norms at EVERY target, including closed gaps and arbitrary size. -/
theorem rawNativeHomeomorph_symm_analytic (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    AnalyticOnNhd ℝ (D.rawNativeHomeomorph t ht).symm univ := by
  intro z _
  let es := physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1))
  let et := physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1/2))
  simpa only [rawNativeHomeomorph, realNativeHomeomorph, realNativeEquiv] using!
    analytic_real_isometry_transport
    (E := physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1/2)))
    (F := physicalRealDeletedSubmodule) (G := physicalRealDeletedSubmodule)
    (H := physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1)))
    et.symm.toContinuousLinearEquiv.toContinuousLinearMap es.toContinuousLinearEquiv.toContinuousLinearMap (D.realNativeInverse t ht) z (D.realNativeInverse_analytic t ht (et.symm z) (mem_univ _))

/-- FULL signed raw coefficient identification with the SAME already-fixed
rough forward map, including BOTH signs and the central zero slot. -/
theorem rawNativeHomeomorph_signed_recovery (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1))) :
    WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (D.rawNativeHomeomorph t ht q).val=
      D.signed (periodOneSobolevImageInclusion t ht q.val) := by
  let es := physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg (t-1))
  let a := es.symm q
  have hs : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a.val=q.val :=
    congrArg Subtype.val (es.apply_symm_apply q)
  change WeightedCoeff.sobolevInclusion _
    (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) (D.realNativeForward t ht a).val)=_
  rw [D.realNativeForward_target_lift,D.realNativeTarget_inclusion]
  change D.signed (periodOneSobolevImageInclusion t ht
    (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a.val))=_
  rw [hs]

theorem rawNativeHomeomorph_inverse_signed_recovery (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (t-1/2))) :
    D.signed (periodOneSobolevImageInclusion t ht ((D.rawNativeHomeomorph t ht).symm z).val)=
      WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) z.val := by
  have h := D.rawNativeHomeomorph_signed_recovery t ht ((D.rawNativeHomeomorph t ht).symm z)
  rw [(D.rawNativeHomeomorph t ht).apply_symm_apply] at h
  exact h.symm

/-- Theorem 1.1(i), with the literal raw source/target domains and
native Banach topologies: for EVERY s>=-1 the SAME actual map restricts
to a global real analytic diffeomorphism H^s_0 -> h^(s+1/2)_0. -/
theorem exists_global_raw_real_analytic_sobolev_diffeomorphism
    (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s) :
    ∃ e : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) ≃ₜ
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2)),
      AnalyticOnNhd ℝ (fun q => e q) univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
      ∀ q, WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) (e q).val=
        D.signed (WeightedCoeff.sobolevInclusion hs q.val) := by
  let P (a b : ℝ) (ha : -1≤a) (hb : (-1/2 : ℝ)≤b) : Prop :=
    ∃ e : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev a) ≃ₜ
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev b),
      AnalyticOnNhd ℝ (fun q => e q) univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
      ∀ q, WeightedCoeff.sobolevInclusion hb (e q).val=
        D.signed (WeightedCoeff.sobolevInclusion ha q.val)
  have reindex (a b : ℝ) (ha : -1≤a) (hb : (-1/2 : ℝ)≤b)
      (hsource : a=s) (htarget : b=s+1/2) (h : P a b ha hb) :
      P s (s+1/2) hs (by linarith) := by
    subst a
    subst b
    exact h
  have ht : 0≤s+1 := by linarith
  apply reindex (s+1-1) (s+1-1/2) (by linarith) (by linarith) (by ring) (by ring)
  exact ⟨D.rawNativeHomeomorph (s+1) ht,D.rawNativeHomeomorph_analytic (s+1) ht,
    D.rawNativeHomeomorph_symm_analytic (s+1) ht,D.rawNativeHomeomorph_signed_recovery (s+1) ht⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
