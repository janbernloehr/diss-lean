import NLS.Articles.KdVPseudomeasures.OriginalHillRoughCanonicalFlow
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Uniform compact-time dependence and precompact full orbits of the
actual canonical rough frequency flow. These are canonical trajectories;
identification with smooth physical PDE solutions remains separate. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def hillRoughCanonicalKdVTimeHomeomorph (time : ℝ) : HillRealMeanZeroSource ≃ₜ HillRealMeanZeroSource where
  toFun := fun q => hillRoughCanonicalKdVFlow q time
  invFun := fun q => hillRoughCanonicalKdVFlow q (-time)
  left_inv q := by dsimp only; rw [hillRoughCanonicalKdVFlow_add,neg_add_cancel,hillRoughCanonicalKdVFlow_zero]
  right_inv q := by dsimp only; rw [hillRoughCanonicalKdVFlow_add,add_neg_cancel,hillRoughCanonicalKdVFlow_zero]
  continuous_toFun := by
    have hi : Continuous (fun q : HillRealMeanZeroSource => (time,q)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hi
  continuous_invFun := by
    have hi : Continuous (fun q : HillRealMeanZeroSource => (-time,q)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hi

def hillRoughCanonicalKdVTrajectory (T : ℝ) (q : HillRealMeanZeroSource) :
    C(Icc (-T) T,HillRealMeanZeroSource) where
  toFun t := hillRoughCanonicalKdVFlow q t.val
  continuous_toFun := by
    have hi : Continuous (fun t : Icc (-T) T => (t.val,q)) := continuous_subtype_val.prodMk continuous_const
    simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hi

theorem continuous_hillRoughCanonicalKdVTrajectory (T : ℝ) :
    Continuous (hillRoughCanonicalKdVTrajectory T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : HillRealMeanZeroSource × Icc (-T) T => hillRoughCanonicalKdVFlow x.1 x.2.val)
  have hi : Continuous (fun x : HillRealMeanZeroSource × Icc (-T) T => (x.2.val,x.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hi

theorem tendsto_hillRoughCanonicalKdVTrajectory
    {ι : Type*} {l : Filter ι} (T : ℝ) (a : ι → HillRealMeanZeroSource)
    (q : HillRealMeanZeroSource) (ha : Tendsto a l (𝓝 q)) :
    Tendsto (fun j => hillRoughCanonicalKdVTrajectory T (a j)) l
      (𝓝 (hillRoughCanonicalKdVTrajectory T q)) :=
  (continuous_hillRoughCanonicalKdVTrajectory T).continuousAt.tendsto.comp ha

theorem tendstoUniformlyOn_hillRoughCanonicalKdVFlow
    {ι : Type*} {l : Filter ι} (T : ℝ) (a : ι → HillRealMeanZeroSource)
    (q : HillRealMeanZeroSource) (ha : Tendsto a l (𝓝 q)) :
    TendstoUniformlyOn (fun j t => hillRoughCanonicalKdVFlow (a j) t)
      (hillRoughCanonicalKdVFlow q) l (Icc (-T) T) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (tendsto_hillRoughCanonicalKdVTrajectory T a q ha)

theorem exists_compact_hillRoughCanonicalKdV_orbit_container (q : HillRealMeanZeroSource) :
    ∃ K : Set HillRealMeanZeroSource, IsCompact K ∧ range (hillRoughCanonicalKdVFlow q) ⊆ K := by
  refine ⟨hillNativeHomeomorph.symm '' hillRealNativeActionTorus q,
    (isCompact_hillRealNativeActionTorus q).image hillNativeHomeomorph.symm.continuous,?_⟩
  rintro _ ⟨time,rfl⟩
  have hd := (hillRealDiscriminantData_eq_iff_native_products (hillRoughCanonicalKdVFlow q time) q).mpr
    (hillRoughCanonicalKdVFlow_products q time)
  refine ⟨hillRealSignedMap (hillRoughCanonicalKdVFlow q time),
    hillRealSignedMap_mem_actionTorus_of_discriminant_eq _ q hd,?_⟩
  exact hillNativeHomeomorph.symm_apply_apply _

theorem isCompact_closure_range_hillRoughCanonicalKdVFlow (q : HillRealMeanZeroSource) :
    IsCompact (closure (range (hillRoughCanonicalKdVFlow q))) := by
  obtain ⟨K,hK,hsub⟩ := exists_compact_hillRoughCanonicalKdV_orbit_container q
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

theorem isBounded_range_hillRoughCanonicalKdVFlow (q : HillRealMeanZeroSource) :
    Bornology.IsBounded (range (hillRoughCanonicalKdVFlow q)) :=
  (isCompact_closure_range_hillRoughCanonicalKdVFlow q).isBounded.subset subset_closure

end NLS.Articles.KdVPseudomeasures
