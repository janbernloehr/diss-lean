import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerCanonicalFlow
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapH1Realization
import NLS.Fourier.SmoothPeriodicCoefficients
import NLS.SequenceSpaces.ExponentEmbedding

/-! Genuine spatial smoothness is preserved by the SAME canonical flow.
All integer strata imply every real Sobolev weight, and the ACTUAL H1
physical synthesis is smooth precisely on this original smooth locus. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem hillReal_has_integer_representative_of_mem_sobolev (N : ℕ) (q : HillRealMeanZeroSource)
    (hq : Memℓp (fun k => (Weight.sobolev (signedStepOrder 0 N) k:ℂ)*
      (hillRealMeanZeroInclusion q).val k) 2) :
    ∃ a : RealSignedHilbert (signedStepOrder 0 N), hillIntegerSourceInclusion N a=q := by
  let s := signedStepOrder 0 N
  have hs : 0 ≤ s := by dsimp only [s]; rw [hillIntegerSobolev_source_order]; positivity
  let b : WeightedCoeff (Weight.sobolev s) 2 :=
    ⟨(hillRealMeanZeroInclusion q).val,hq⟩
  have hw : ∀ k, Weight.signedSobolev s k ≤ 1*Weight.sobolev s k := by
    intro k
    simpa only [one_mul] using Weight.signedSobolev_le_sobolev s hs k
  let v := WeightComparison.map (Weight.sobolev s) (Weight.signedSobolev s) 1 zero_le_one hw b
  have hv (k : ℤ) : v.val k=q.val.val.val k :=
    WeightComparison.map_apply _ _ 1 zero_le_one hw b k
  let a : RealSignedHilbert s := ⟨⟨v,by change v.val 0=0; rw [hv]; exact q.val.property⟩,by
    intro k
    change v.val (-k)=(starRingEnd ℂ) (v.val k)
    rw [hv,hv]
    exact q.property k⟩
  refine ⟨a,?_⟩
  apply hillRealMeanZeroInclusion_injective
  apply Subtype.ext
  funext k
  change (hillIntegerSourceInclusion N a).val.val.val k=q.val.val.val k
  rw [hillIntegerSourceInclusion_apply]
  exact hv k

theorem hillIntegerSourceInclusion_mem_sobolev (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 N)) (s : ℝ) (hs : s≤(N:ℝ)) :
    Memℓp (fun k => (Weight.sobolev s k:ℂ)*(hillRealMeanZeroInclusion (hillIntegerSourceInclusion N q)).val k) 2 := by
  let t := signedStepOrder 0 N
  have ht : 0≤t := by dsimp only [t]; rw [hillIntegerSobolev_source_order]; positivity
  let b := physicalSignedSobolevPositiveEquiv t ht 2 q
  let c := sobolevInclusion (show s≤t by dsimp only [t]; rw [hillIntegerSobolev_source_order]; exact hs) b.val.val
  have hc (k : ℤ) : c.val k=(hillRealMeanZeroInclusion (hillIntegerSourceInclusion N q)).val k := by
    rw [sobolevInclusion_apply,physicalSignedSobolevPositiveEquiv_apply]
    exact (hillIntegerSourceInclusion_apply N q k).symm
  have hm : Memℓp (fun k => (Weight.sobolev s k:ℂ)*c.val k) 2 := c.property
  simpa only [hc] using hm

theorem hillH1Smooth_mem_hillRealSmoothLocus (q : RealSignedHilbert (signedStepOrder 0 1))
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2:ℝ)))) :
    hillIntegerSourceInclusion 1 q ∈ hillRealSmoothLocus := by
  intro s hs
  let f := fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2:ℝ))
  let b : WeightedCoeff (Weight.sobolev s) 1 := ⟨periodOneCoefficient f,
    memlp_periodOneCoefficient_sobolev_one s hs f hq (periodOneSobolevSynthesis_periodic _)⟩
  let c := WeightedCoeff.exponentInclusion (Weight.sobolev s) (by norm_num : (1:ℝ≥0∞)≤2) b
  have hc (k : ℤ) : c.val k=(hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)).val k := by
    rw [WeightedCoeff.exponentInclusion_apply]
    change periodOneCoefficient f k=_
    rw [periodOneCoefficient_periodOneSobolevSynthesis,signedOneRealToScalarDomain_apply]
    exact (hillIntegerSourceInclusion_apply 1 q k).symm
  have hm : Memℓp (fun k => (Weight.sobolev s k:ℂ)*c.val k) 2 := c.property
  simpa only [hc] using hm

theorem contDiff_hillH1_physical_synthesis_of_smooth_locus (q : RealSignedHilbert (signedStepOrder 0 1))
    (hq : hillIntegerSourceInclusion 1 q ∈ hillRealSmoothLocus) :
    ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2:ℝ))) := by
  apply contDiff_periodOneSynthesis_of_all_sobolev (p:=2) (by simp)
    (sobolevToL1CLM 2 (by simp) (signedOneRealToScalarDomain q))
  intro s hs
  have h := hq s hs
  convert! h using 1
  funext k
  rw [sobolevToL1CLM_apply,signedOneRealToScalarDomain_apply]
  exact congrArg (fun z : ℂ => (Weight.sobolev s k:ℂ)*z) (hillIntegerSourceInclusion_apply 1 q k).symm

theorem hillRoughCanonicalKdVFlow_preserves_smooth_locus (q : HillRealMeanZeroSource)
    (hq : q ∈ hillRealSmoothLocus) (time : ℝ) :
    hillRoughCanonicalKdVFlow q time ∈ hillRealSmoothLocus := by
  intro s hs
  let N := ⌈s⌉₊
  obtain ⟨a,ha⟩ := hillReal_has_integer_representative_of_mem_sobolev N q
    (hq (signedStepOrder 0 N) (by rw [hillIntegerSobolev_source_order]; positivity))
  have h := hillIntegerSourceInclusion_mem_sobolev N (hillIntegerCanonicalKdVFlow N a time) s (Nat.le_ceil s)
  rw [hillIntegerCanonicalKdVFlow_inclusion,ha] at h
  exact h

end NLS.Articles.KdVPseudomeasures
