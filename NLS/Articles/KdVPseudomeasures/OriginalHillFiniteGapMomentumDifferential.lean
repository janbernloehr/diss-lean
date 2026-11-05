import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMomentumVector
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapRegularity
import NLS.Poisson.GardnerCotangentKernel

/-! The exact finite weighted action differential at an ACTUAL finite-gap
source is the original momentum differential on EVERY mean-zero Banach
direction. The constant cotangent kernel is treated explicitly. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson
namespace NLS.Articles.KdVPseudomeasures

theorem finite_action_differential_eq_sobolev_pairing
    (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k)
    (s : Finset ℕ+)
    (hvec : v=∑ n ∈ s, (2*Real.pi*(n:ℕ)) • hillRealActionHamiltonianVector n q)
    (b : WeightedCoeff (Weight.sobolev 1) 2) (hb : ∀ k : ℤ, b.val k=q.val.val.val k)
    (h : HillRealMeanZeroSource) :
    (∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ)*
      ((fderiv ℂ (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion q)) (hillRealMeanZeroInclusion h)))=
        WeightedCoeff.sobolevBilinearPairing 1 b (hillRealMeanZeroInclusion h) := by
  let a : WeightedCoeff (Weight.sobolev 1) 2 :=
    ∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ) • hminusScalarGradient (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion q)
  have hi := congrArg hillRealMeanZeroInclusion hvec
  rw [map_sum] at hi
  simp_rw [map_smul,hillRealActionHamiltonianVector_inclusion] at hi
  have ha : gardnerDerivative a=hillRealMeanZeroInclusion v := by
    dsimp only [a]
    rw [map_sum]
    simp_rw [map_smul]
    change (∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ) • hillHminusActionHamiltonianVector n (hillRealMeanZeroInclusion q))= _
    rw [hi]
    apply Finset.sum_congr rfl
    intro n hn
    exact algebraMap_smul ℂ (2*Real.pi*(n:ℕ)) _
  have hba : gardnerDerivative b=hillRealMeanZeroInclusion v := by
    apply Subtype.ext
    funext k
    rw [gardnerDerivative_apply,hb]
    change (2*Real.pi:ℂ)*I*k*q.val.val.val k=v.val.val.val k
    rw [hv]
    push_cast
    ring
  have hp := sobolevBilinearPairing_eq_of_gardnerDerivative_eq a b (ha.trans hba.symm)
    (hillRealMeanZeroInclusion h) h.val.property
  have he : WeightedCoeff.sobolevBilinearPairing 1 a (hillRealMeanZeroInclusion h)=
      ∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ)*
        ((fderiv ℂ (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion q)) (hillRealMeanZeroInclusion h)) := by
    change ((WeightedCoeff.sobolevBilinearPairing (p:=2) (q:=2) 1).flip (hillRealMeanZeroInclusion h)) a= _
    dsimp only [a]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_smul]
    change ((2*Real.pi*(n:ℕ):ℝ):ℂ)*
      WeightedCoeff.sobolevBilinearPairing 1 (hminusScalarGradient (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion q))
        (hillRealMeanZeroInclusion h)= _
    rw [← hminusScalarGradient_represents]
  rw [he] at hp
  exact hp

/-- At EVERY actual finite-gap L2 source, one finite set contains ALL open
native modes and its exact weighted action differential is the original
momentum differential on ALL original mean-zero Hminus directions. -/
theorem exists_hillL2_finite_action_momentum_differential (u : HillRealL2BanachSource)
    (hf : hillL2SourceInclusion u ∈ hillRealFiniteGapLocus) :
    ∃ b : WeightedCoeff (Weight.sobolev 1) 2,
      (∀ k : ℤ, b.val k=(hillL2SourceInclusion u).val.val.val k) ∧
      ∃ s : Finset ℕ+,
        (∀ n : ℕ+, n ∉ s → (hillRealSignedMap (hillL2SourceInclusion u)).val.val.val (n:ℤ)=0) ∧
        ∀ h : HillRealMeanZeroSource,
          (∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ)*
            ((fderiv ℂ (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion (hillL2SourceInclusion u)))
              (hillRealMeanZeroInclusion h)))=
            WeightedCoeff.sobolevBilinearPairing 1 b (hillRealMeanZeroInclusion h) := by
  let b : WeightedCoeff (Weight.sobolev 1) 2 :=
    ⟨(hillRealMeanZeroInclusion (hillL2SourceInclusion u)).val,
      hillRealFiniteGap_mem_all_sobolev _ hf 1 (by norm_num)⟩
  obtain ⟨s,hs,hvec⟩ := exists_hillL2_finite_action_spatialGenerator u hf
  refine ⟨b,fun _ => rfl,s,hs,fun h => ?_⟩
  exact finite_action_differential_eq_sobolev_pairing (hillL2SourceInclusion u)
    (hillL2SourceSpatialGenerator u) (fun k => by rw [hillL2SourceSpatialGenerator_apply,hillL2SourceInclusion_apply])
    s hvec b (fun _ => rfl) h

end NLS.Articles.KdVPseudomeasures
