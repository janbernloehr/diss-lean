import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapApproximation
import NLS.Articles.KdVKdV2Frequencies.NativeAllGapFrequencyMoments
import NLS.KdV.HillIntrinsicMomentContinuity

/-! # Actual physical spectral moment limits at every native source

Every fixed moment and finite head converges to the ORIGINAL source moment.
The diagonal finite formulas along genuine finite-gap approximations converge
to the ACTUAL intrinsic Hamiltonian frequencies, also at infinite-gap sources.
Exchanging this limit with the infinite sum at the fixed source remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Each actual physical contour moment converges at every original native
source, including arbitrary closed own or integration gaps. -/
theorem tendsto_nativeFiniteGapApproximation_moment (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n k : ℕ+) (b : ℕ) :
    let p := fun N => nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
      (D.nativeFiniteGapApproximation m q N).property.1
    Tendsto (fun N => hillIntrinsicFrequencyMoment (p N).val (p N).property.1 (p N).property.2 n n.pos k b)
      atTop (𝓝 (hillIntrinsicFrequencyMoment (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n n.pos k b)) :=
  (continuous_hillIntrinsicFrequencyMoment n k b).continuousAt.tendsto.comp
    (D.tendsto_nativeFiniteGapApproximation_physical m q)

/-- The complete finite moment head converges in the actual physical source topology. -/
theorem tendsto_nativeFiniteGapApproximation_moment_head (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) (a b L : ℕ) :
    Tendsto (fun N => hillIntrinsicWeightedMomentPartialSum
      (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
        (D.nativeFiniteGapApproximation m q N).property.1) n a b L)
      atTop (𝓝 (hillIntrinsicWeightedMomentPartialSum (nativeHillPhysicalSource m q.val q.property.1) n a b L)) :=
  (continuous_hillIntrinsicWeightedMomentPartialSum n a b L).continuousAt.tendsto.comp
    (D.tendsto_nativeFiniteGapApproximation_physical m q)

/-- At each genuine finite-gap approximant, the ACTUAL KdV frequency
correction is the finite original moment sum with exactly the same cutoff. -/
theorem nativeFiniteGapApproximation_kdv_finite_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (N : ℕ) (n : ℕ+) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) (D.nativeFiniteGapApproximation 1 q N) n : ℂ)-
      (2*(n : ℂ)*Real.pi)^3 = -12*hillIntrinsicWeightedMomentPartialSum
        (nativeHillPhysicalSource 1 (D.nativeFiniteGapApproximation 1 q N).val
          (D.nativeFiniteGapApproximation 1 q N).property.1) n 1 2 N := by
  let u := D.nativeFiniteGapApproximation 1 q N
  let p := nativeHillPhysicalSource 1 u.val u.property.1
  obtain ⟨S,hS⟩ := D.nativeFiniteGapApproximation_finite_gap 1 q N
  have he := D.native_finiteGap_kdv_frequency_moments_all_gaps u S hS n
  have hc : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 :=
    fun k hk hNk => D.nativeFiniteGapApproximation_closed_tail 1 q N ⟨k,by omega⟩ hNk
  have hs := (hasSum_hillIntrinsicFrequencyMoment_closed_tail p.val p.property.1 p.property.2
    n n.pos N hc (fun k => (k : ℂ)) (by norm_num) 1).tsum_eq
  rw [hs] at he
  simpa only [hillIntrinsicWeightedMomentPartialSum,pow_one] using he

/-- The physical KdV2 formula at the same exact finite cutoff, including
both moment weights and the independent original physical mass. -/
theorem nativeFiniteGapApproximation_kdv2_finite_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (N : ℕ) (n : ℕ+) :
    let u := D.nativeFiniteGapApproximation 2 q N
    let p := nativeHillPhysicalSource 2 u.val u.property.1
    (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) u n : ℂ)-
      20*(2*(n : ℂ)*Real.pi)*nativeMiuraMass 2 u.val-(2*(n : ℂ)*Real.pi)^5 =
      -160*(Real.pi : ℂ)^2*hillIntrinsicWeightedMomentPartialSum p n 3 2 N+
        80*hillIntrinsicWeightedMomentPartialSum p n 1 4 N := by
  dsimp only
  let u := D.nativeFiniteGapApproximation 2 q N
  let p := nativeHillPhysicalSource 2 u.val u.property.1
  obtain ⟨S,hS⟩ := D.nativeFiniteGapApproximation_finite_gap 2 q N
  have he := D.native_finiteGap_kdv2_frequency_moments_all_gaps u S hS n
  have hc : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 :=
    fun k hk hNk => D.nativeFiniteGapApproximation_closed_tail 2 q N ⟨k,by omega⟩ hNk
  have hs2 := (hasSum_hillIntrinsicFrequencyMoment_closed_tail p.val p.property.1 p.property.2
    n n.pos N hc (fun k => (k : ℂ)^3) (by norm_num) 1).tsum_eq
  have hs4 := (hasSum_hillIntrinsicFrequencyMoment_closed_tail p.val p.property.1 p.property.2
    n n.pos N hc (fun k => (k : ℂ)) (by norm_num) 3).tsum_eq
  rw [hs2,hs4] at he
  simpa only [hillIntrinsicWeightedMomentPartialSum,pow_one] using he

/-- At EVERY original native H1 source, including infinite-gap sources,
the diagonal finite physical moment formulas converge to the TRUE frequency correction. -/
theorem tendsto_kdv_finite_spectral_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (n : ℕ+) :
    Tendsto (fun N => -12*hillIntrinsicWeightedMomentPartialSum
      (nativeHillPhysicalSource 1 (D.nativeFiniteGapApproximation 1 q N).val
        (D.nativeFiniteGapApproximation 1 q N).property.1) n 1 2 N) atTop
      (𝓝 ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)) := by
  have hω := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (D.tendsto_nativeFiniteGapApproximation_frequency 1 3 (by norm_num) q n)
  exact (hω.sub tendsto_const_nhds).congr' (Eventually.of_forall
    (fun N => D.nativeFiniteGapApproximation_kdv_finite_moments q N n))

/-- At EVERY original native H2 source the genuine finite spectral formulas
converge to the ACTUAL mass-renormalized physical KdV2 frequency. -/
theorem tendsto_kdv2_finite_spectral_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (n : ℕ+) :
    Tendsto (fun N =>
      let u := D.nativeFiniteGapApproximation 2 q N
      let p := nativeHillPhysicalSource 2 u.val u.property.1
      (-160*(Real.pi : ℂ)^2*hillIntrinsicWeightedMomentPartialSum p n 3 2 N+
        80*hillIntrinsicWeightedMomentPartialSum p n 1 4 N)) atTop
      (𝓝 ((D.nativeSourceHierarchyFrequency 2 5 (by norm_num) q n : ℂ)-
        20*(2*(n : ℂ)*Real.pi)*nativeMiuraMass 2 q.val-(2*(n : ℂ)*Real.pi)^5)) := by
  have hω := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (D.tendsto_nativeFiniteGapApproximation_frequency 2 5 (by norm_num) q n)
  have hmass := (analyticAt_nativeMiuraMass 2 q.val).continuousAt.tendsto.comp
    (continuous_subtype_val.continuousAt.tendsto.comp (D.tendsto_nativeFiniteGapApproximation 2 q))
  have hlim := (hω.sub ((tendsto_const_nhds (x := 20*(2*(n : ℂ)*Real.pi))).mul hmass)).sub
    (tendsto_const_nhds (x := (2*(n : ℂ)*Real.pi)^5))
  exact hlim.congr' (Eventually.of_forall (fun N => D.nativeFiniteGapApproximation_kdv2_finite_moments q N n))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
