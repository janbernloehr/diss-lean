import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapModeOpening
import NLS.Articles.KdVKdV2Frequencies.NativeDirichletFrequencyContinuity
import NLS.Articles.KdVKdV2Frequencies.NativeFrequencyContinuity

/-! # Intrinsic finite-gap frequencies at closed as well as open own modes

Actual higher-native finite-gap inverse perturbations open a closed mode.
Both independently defined frequency expressions converge in their proved
native topologies. Thus no vanishing coordinate is cancelled at a closed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- An actual open-mode finite-gap identity extends through the selected
closed gap whenever its other side is continuous in a stronger native norm.
The required finite-gap approximations and all source comparisons are PROVED. -/
theorem native_finiteGap_frequency_eq_of_open_identity (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2)) (M : ℕ) (hMm : m≤M)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 k=0)
    (n : ℕ+) (G : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) → ℂ)
    (hG : Continuous (fun p => G (physicalRealMeanZeroSobolevInclusion
      (show (m : ℝ)≤(M : ℝ) by exact_mod_cast hMm) p)))
    (he : ∀ p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)),
      (∀ k : ℕ+, k ∉ insert n S → hillRealGapHalfLength
        (nativeHillPhysicalSource m p.val p.property.1).val
        (nativeHillPhysicalSource m p.val p.property.1).property.1
        (nativeHillPhysicalSource m p.val p.property.1).property.2 k=0) →
      hillRealGapHalfLength (nativeHillPhysicalSource m p.val p.property.1).val
        (nativeHillPhysicalSource m p.val p.property.1).property.1
        (nativeHillPhysicalSource m p.val p.property.1).property.2 n≠0 →
      (D.nativeSourceHierarchyFrequency m r hrs p n : ℂ)=G p) :
    (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ)=G q := by
  classical
  by_cases hc : hillRealGapHalfLength (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n=0
  · obtain ⟨p,hpq,hphys⟩ := native_finiteGap_exists_all_order_lift m M q S hq
    let L := physicalRealMeanZeroSobolevInclusion (show (m : ℝ)≤(M : ℝ) by exact_mod_cast hMm)
    let v := D.nativeModeOpening M p n
    let u := fun t : ℝ => L (v t)
    have hpS : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
        (nativeHillPhysicalSource M p.val p.property.1).val
        (nativeHillPhysicalSource M p.val p.property.1).property.1
        (nativeHillPhysicalSource M p.val p.property.1).property.2 k=0 := by
      simpa only [hphys] using hq
    have hpc : hillRealGapHalfLength (nativeHillPhysicalSource M p.val p.property.1).val
        (nativeHillPhysicalSource M p.val p.property.1).property.1
        (nativeHillPhysicalSource M p.val p.property.1).property.2 n=0 := by
      simpa only [hphys] using hc
    have hsource (a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (M : ℝ))) :
        nativeHillPhysicalSource m (L a).val (L a).property.1=nativeHillPhysicalSource M a.val a.property.1 :=
      nativeHillPhysicalSource_eq_of_coefficients m M (L a).val a.val (L a).property.1 a.property.1
        (fun j => physicalRealMeanZeroSobolevInclusion_coefficient _ a j)
    have hLp : L p=q := by
      apply Subtype.ext
      apply Subtype.ext
      funext j
      rw [physicalRealMeanZeroSobolevInclusion_coefficient]
      exact hpq j
    have hu0 : u 0=q := by simp only [u,v,D.nativeModeOpening_zero,hLp]
    have hv : Continuous v := D.continuous_nativeModeOpening M p n
    have hu : Continuous u := L.continuous.comp hv
    have hF : Continuous (fun t : ℝ => (D.nativeSourceHierarchyFrequency m r hrs (u t) n : ℂ)) :=
      Complex.continuous_ofReal.comp ((D.continuous_nativeSourceHierarchyFrequency m r hrs n).comp hu)
    have hGG : Continuous (fun t : ℝ => G (u t)) := by
      simpa only [u,L,Function.comp_def] using! hG.comp hv
    have heq : (fun t : ℝ => (D.nativeSourceHierarchyFrequency m r hrs (u t) n : ℂ)) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun t => G (u t)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply he (u t)
      · intro k hk
        rw [show nativeHillPhysicalSource m (u t).val (u t).property.1=
          nativeHillPhysicalSource M (v t).val (v t).property.1 from hsource (v t)]
        exact D.nativeModeOpening_finite_gap M p S hpS n t k hk
      · rw [show nativeHillPhysicalSource m (u t).val (u t).property.1=
          nativeHillPhysicalSource M (v t).val (v t).property.1 from hsource (v t)]
        exact D.nativeModeOpening_gap_open M p n hpc t ht
    have hlim := tendsto_nhds_unique
      (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hGG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
    simpa only [hu0] using hlim
  · apply he q
    · intro k hk
      exact hq k (fun hs => hk (Finset.mem_insert_of_mem hs))
    · exact hc

/-- The actual physical KdV frequency equals its actual finite Dirichlet sum
at EVERY own mode, including all collapsed selected gaps. -/
theorem native_finiteGap_kdv_frequency_eq_dirichlet_all_gaps (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 k=0)
    (N : ℕ) (hSN : ∀ k ∈ S, (k : ℕ)≤N) (n : ℕ+) (hnN : (n : ℕ)≤N) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)=nativeKdVDirichletFrequency q N n := by
  apply D.native_finiteGap_frequency_eq_of_open_identity 1 3 (by norm_num) 3 (by decide) q S hq n
    (fun p => nativeKdVDirichletFrequency p N n)
    ((continuous_nativeKdVDirichletFrequency N n).comp (physicalRealMeanZeroSobolevInclusion (by norm_num : ((1 : ℕ) : ℝ)≤((3 : ℕ) : ℝ))).continuous)
  intro p hp hopen
  apply D.native_finiteGap_kdv_frequency_eq_dirichlet p (insert n S) hp N _ n hopen
  intro k hk
  rcases Finset.mem_insert.mp hk with he|he
  · simpa only [he] using hnN
  · exact hSN k he

/-- The SAME complete identification for the actual physical KdV2 frequency,
including every closed own gap and the original native H2 source domain. -/
theorem native_finiteGap_kdv2_frequency_eq_dirichlet_all_gaps (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 k=0)
    (N : ℕ) (hSN : ∀ k ∈ S, (k : ℕ)≤N) (n : ℕ+) (hnN : (n : ℕ)≤N) :
    (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) q n : ℂ)=nativeKdV2DirichletFrequency q N n := by
  apply D.native_finiteGap_frequency_eq_of_open_identity 2 5 (by norm_num) 3 (by decide) q S hq n
    (fun p => nativeKdV2DirichletFrequency p N n)
    (continuous_nativeKdV2DirichletFrequency_higher 3 (by decide) N n)
  intro p hp hopen
  apply D.native_finiteGap_kdv2_frequency_eq_dirichlet p (insert n S) hp N _ n hopen
  intro k hk
  rcases Finset.mem_insert.mp hk with he|he
  · simpa only [he] using hnN
  · exact hSN k he

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
