import NLS.Articles.KdVPseudomeasures.OriginalHillWienerPhaseTrajectory
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalRoughFlow
import NLS.ComplexAnalysis.ContinuousMapSuperposition

/-! The SAME original physical KdV flow preserves every integer-order
Wiener space. Its compact-time trajectories are continuous in the
original strong Wiener norm. Uniform Banach analyticity of the inverse
superposition is a separate obligation. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def originalWienerCanonicalKdVFlow (N : ℕ) (q : OriginalWienerPotential N) (time : ℝ) : OriginalWienerPotential N :=
  (originalHillWienerEquiv N).symm
    (fourierRealZeroPhaseFlow (Weight.sobolev (signedStepOrder (1/2) N))
      (originalWienerSignedKdVFrequency N q) (originalWienerSignedKdVFrequency_neg N q)
      time (originalHillWienerEquiv N q))

theorem originalWienerCanonicalKdVFlow_native (N : ℕ) (q : OriginalWienerPotential N) (time : ℝ) :
    originalHillRealMeanZeroSource (originalWienerOriginalPotential N (originalWienerCanonicalKdVFlow N q time)) =
      hillRoughCanonicalKdVFlow (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)) time := by
  apply injective_hillRealSignedMap
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [← originalHillWienerEquiv_apply,hillRoughCanonicalKdVFlow_native]
  change ((originalHillWienerEquiv N) ((originalHillWienerEquiv N).symm _)).val.val.val k = _
  rw [Equiv.apply_symm_apply,fourierRealZeroPhaseFlow_apply,
    fourierRealZeroPhaseFlow_apply,originalHillWienerEquiv_apply]
  rfl

theorem originalWienerCanonicalKdVFlow_original (N : ℕ) (q : OriginalWienerPotential N) (time : ℝ) :
    originalWienerOriginalPotential N (originalWienerCanonicalKdVFlow N q time) =
      hillOriginalCanonicalKdVFlow (originalWienerOriginalPotential N q) time := by
  rw [← originalHillPotentialOfRealSource_ofOriginal
    (originalWienerOriginalPotential N (originalWienerCanonicalKdVFlow N q time)),
      originalWienerCanonicalKdVFlow_native]
  rfl

theorem originalWienerOriginalPotential_injective (N : ℕ) :
    Function.Injective (originalWienerOriginalPotential N) := by
  intro a b hab
  have h := congrArg (fun q : OriginalHminusOnePotential => q.val.val) hab
  rw [originalWienerOriginalPotential_same_distribution,originalWienerOriginalPotential_same_distribution] at h
  exact Subtype.ext (Subtype.ext h)

theorem originalWienerCanonicalKdVFlow_zero (N : ℕ) (q : OriginalWienerPotential N) :
    originalWienerCanonicalKdVFlow N q 0=q := by
  apply originalWienerOriginalPotential_injective N
  rw [originalWienerCanonicalKdVFlow_original,hillOriginalCanonicalKdVFlow_zero]

theorem originalWienerCanonicalKdVFlow_add (N : ℕ) (q : OriginalWienerPotential N) (t s : ℝ) :
    originalWienerCanonicalKdVFlow N (originalWienerCanonicalKdVFlow N q s) t =
      originalWienerCanonicalKdVFlow N q (t+s) := by
  apply originalWienerOriginalPotential_injective N
  rw [originalWienerCanonicalKdVFlow_original,originalWienerCanonicalKdVFlow_original,
    hillOriginalCanonicalKdVFlow_add,originalWienerCanonicalKdVFlow_original]

private theorem continuous_inverse (N : ℕ) : Continuous (originalHillWienerEquiv N).symm :=
  continuous_iff_continuousAt.mpr (analyticAt_originalHillWienerEquiv_symm N · |>.continuousAt)

variable {K : Type} [TopologicalSpace K] [CompactSpace K]
local instance (N : ℕ) : NormedSpace ℝ C(K,OriginalWienerTarget N) :=
  @ContinuousMap.normedSpace K (OriginalWienerTarget N) inferInstance inferInstance
    inferInstance ℝ inferInstance (fourierRealZeroSubmodule_normedSpace _)

def originalWienerKdVTrajectory (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) :
    C(K,OriginalWienerPotential N) :=
  ⟨fun t => (originalHillWienerEquiv N).symm (originalWienerKdVCoordinateTrajectory N θ q t),
    (continuous_inverse N).comp (originalWienerKdVCoordinateTrajectory N θ q).continuous⟩

theorem originalWienerKdVTrajectory_apply (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) (t : K) :
    originalWienerKdVTrajectory N θ q t=originalWienerCanonicalKdVFlow N q (θ t) := by
  change (originalHillWienerEquiv N).symm (originalWienerKdVCoordinateTrajectory N θ q t) = _
  rw [originalWienerKdVCoordinateTrajectory_phase]
  rfl

theorem originalWienerKdVTrajectory_original (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) (t : K) :
    originalWienerOriginalPotential N (originalWienerKdVTrajectory N θ q t) =
      hillOriginalCanonicalKdVFlow (originalWienerOriginalPotential N q) (θ t) := by
  rw [originalWienerKdVTrajectory_apply,originalWienerCanonicalKdVFlow_original]

theorem continuous_originalWienerKdVTrajectory (N : ℕ) (θ : C(K,ℝ)) :
    Continuous (originalWienerKdVTrajectory N θ) := by
  have hS : Continuous (superposition (K := K) (originalHillWienerEquiv N).symm) := by
    have h := continuousOn_superposition (K := K) (U := univ) (continuous_inverse N).continuousOn
    have he : {g : C(K,OriginalWienerTarget N) | range g ⊆ (univ : Set (OriginalWienerTarget N))}=univ := by
      ext g
      simp only [mem_ofPred_eq,subset_univ,mem_univ]
    rw [he] at h
    exact continuousOn_univ.mp h
  have hC : Continuous (originalWienerKdVCoordinateTrajectory N θ) :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_originalWienerKdVCoordinateTrajectory N θ q).continuousAt)
  apply (hS.comp hC).congr
  intro q
  apply ContinuousMap.ext
  intro t
  exact superposition_apply (U := univ) (continuous_inverse N).continuousOn (subset_univ _) t

end NLS.Articles.KdVPseudomeasures
