import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalRealInverse
import NLS.KdV.HillNativeFiniteGap

/-! Actual native finite-gap approximation in the original physical
Hminus-one norm, obtained by pulling symmetric output truncations back
through the actual physical real local inverse. Collisions reduce to
actual finite-gap collisions without transferring an NLS density theorem. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- The actual local inverse realizes finite native outputs and converges
back to the original physical source in its full Hminus-one norm. -/
theorem hillPhysicalNativeFiniteGap_approximation (q : HillRealMeanZeroSource) :
    ∃ g : HillRealSignedTarget → HillRealMeanZeroSource,
      AnalyticAt ℝ g (hillRealSignedMap q) ∧ g (hillRealSignedMap q)=q ∧
      Tendsto (fun N : ℕ => g (WeightedCoeff.fourierRealZeroTruncate
        (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q))) atTop (𝓝 q) ∧
      ∀ᶠ N : ℕ in atTop,
        g (WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q)) ∈ hillRealFiniteGapLocus ∧
        hillRealSignedMap (g (WeightedCoeff.fourierRealZeroTruncate
          (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q)))=
            WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q) := by
  obtain ⟨g,hg,hgq,_,hright,_⟩ := hillPhysicalNativeMap_localInverse q
  have ht := WeightedCoeff.tendsto_fourierRealZeroTruncate (p := 2) (by simp)
    (Weight.signedSobolev (-1/2)) (hillRealSignedMap q)
  have hgt := hg.continuousAt.tendsto.comp ht
  rw [hgq] at hgt
  refine ⟨g,hg,hgq,hgt,?_⟩
  filter_upwards [ht.eventually hright] with N hN
  exact ⟨hillRealFiniteGap_of_map_eq_truncate _ _ N hN,hN⟩

/-- The ACTUAL native finite-gap locus is dense in the physical Hminus-one norm. -/
theorem dense_hillRealFiniteGapLocus : Dense hillRealFiniteGapLocus := by
  intro q
  obtain ⟨g,_,_,hgt,hfinite⟩ := hillPhysicalNativeFiniteGap_approximation q
  exact mem_closure_of_tendsto hgt (hfinite.mono fun _ h => h.1)

/-- Two distinct sources with the same actual native output give distinct
finite-gap collisions in any independently prescribed open neighborhoods. -/
theorem hillPhysicalNative_finiteGap_collision_mem_open
    (q p : HillRealMeanZeroSource) (hne : q ≠ p) (heq : hillRealSignedMap q=hillRealSignedMap p)
    (U V : Set HillRealMeanZeroSource) (hU : IsOpen U) (hV : IsOpen V) (hqU : q ∈ U) (hpV : p ∈ V) :
    ∃ N : ℕ, ∃ q' p' : HillRealMeanZeroSource,
      q' ∈ U ∧ p' ∈ V ∧ q' ≠ p' ∧ q' ∈ hillRealFiniteGapLocus ∧ p' ∈ hillRealFiniteGapLocus ∧
      hillRealSignedMap q'=WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q) ∧
      hillRealSignedMap p'=WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q) := by
  obtain ⟨g,hg,hgq,_,hrightg,_⟩ := hillPhysicalNativeMap_localInverse q
  obtain ⟨k,hk,hkp,_,hrightk,_⟩ := hillPhysicalNativeMap_localInverse p
  rw [← heq] at hk hkp hrightk
  let T := fun N : ℕ => WeightedCoeff.fourierRealZeroTruncate
    (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q)
  have ht : Tendsto T atTop (𝓝 (hillRealSignedMap q)) :=
    WeightedCoeff.tendsto_fourierRealZeroTruncate (by simp) _ _
  have hgT : Tendsto (fun N => g (T N)) atTop (𝓝 q) := by
    have h := hg.continuousAt.tendsto.comp ht
    rwa [hgq] at h
  have hkT : Tendsto (fun N => k (T N)) atTop (𝓝 p) := by
    have h := hk.continuousAt.tendsto.comp ht
    rwa [hkp] at h
  have hdistinct : ∀ᶠ N in atTop, g (T N) ≠ k (T N) := by
    simpa only [sub_ne_zero] using (hgT.sub hkT).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨N,hgu,hkv,hneq,hgr,hkr⟩ :=
    ((hgT.eventually (hU.mem_nhds hqU)).and
      ((hkT.eventually (hV.mem_nhds hpV)).and
        (hdistinct.and ((ht.eventually hrightg).and (ht.eventually hrightk))))).exists
  exact ⟨N,g (T N),k (T N),hgu,hkv,hneq,
    hillRealFiniteGap_of_map_eq_truncate _ _ N hgr,
    hillRealFiniteGap_of_map_eq_truncate _ _ N hkr,hgr,hkr⟩

/-- Global injectivity of the actual native map is equivalent to injectivity
on its actual finite-gap locus. This is a reduction, not an injectivity claim. -/
theorem hillPhysicalNative_injective_iff_injOn_finiteGap :
    Function.Injective hillRealSignedMap ↔ Set.InjOn hillRealSignedMap hillRealFiniteGapLocus := by
  constructor
  · intro hi
    exact hi.injOn
  · intro hi q p heq
    by_contra hne
    obtain ⟨_,q',p',_,_,hneq,hfq,hfp,hq',hp'⟩ :=
      hillPhysicalNative_finiteGap_collision_mem_open q p hne heq univ univ
        isOpen_univ isOpen_univ (mem_univ _) (mem_univ _)
    exact hneq (hi hfq hfp (hq'.trans hp'.symm))

end NLS.Articles.KdVPseudomeasures
