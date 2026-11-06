import NLS.KdV.HillOriginalWeightedMeanZeroSource
import NLS.KdV.HillHomogeneousSpectralSequence

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

/-- An exact homogeneous target representative from the actual physical
Cartesian sequence; every lower order uses the same source and same map. -/
def hillBirkhoffSobolevRepresentative (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) : HillBirkhoffSobolevSpace m :=
  (RealWeightedNatPair.normalizationEquiv _ _).symm
    (hillHomogeneousSpectralSequence (by simp) (by intro k; simp) M m hm p)

theorem hillBirkhoffSobolevRepresentative_coordinates (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) (k : ℕ) :
    (hillBirkhoffSobolevRepresentative M m hm p).val k =
      (hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean)).val k := by
  rw [hillOriginalBirkhoffMap_coordinates]
  apply RealWeightedNatPair.normalization_symm_apply_of_mul
  rfl

/-- The SAME fixed original real Birkhoff map takes its integer Sobolev
source into every claimed exact homogeneous target space. -/
theorem hillOriginalBirkhoffMap_mem_sobolev (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    (hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean)).val ∈
      realWeightedNatPairSubmodule (hillBirkhoffSobolevWeight m) := by
  have he : (hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean)).val =
      (hillBirkhoffSobolevRepresentative M m hm p).val :=
    funext (fun k => (hillBirkhoffSobolevRepresentative_coordinates M m hm p hmean k).symm)
  rw [he]
  exact (hillBirkhoffSobolevRepresentative M m hm p).property

/-- Literal higher-norm restriction of the ONE fixed original map. -/
def hillOriginalBirkhoffSobolevRestriction (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    HillBirkhoffSobolevSpace m :=
  ⟨(hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean)).val,
    hillOriginalBirkhoffMap_mem_sobolev M m hm p hmean⟩

/-- Exact equality with the already checked physical target norm, with
homogeneous (2*pi*n)^(2m+1) rather than the source's inhomogeneous weights. -/
theorem norm_hillOriginalBirkhoffSobolevRestriction (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    ‖hillOriginalBirkhoffSobolevRestriction M m hm p hmean‖ =
      ‖hillHomogeneousSpectralSequence (by simp) (by intro k; simp) M m hm p‖ := by
  have he : hillOriginalBirkhoffSobolevRestriction M m hm p hmean = hillBirkhoffSobolevRepresentative M m hm p := by
    apply Subtype.ext
    exact funext (fun k => (hillBirkhoffSobolevRepresentative_coordinates M m hm p hmean k).symm)
  rw [he]
  exact (RealWeightedNatPair.normalizationIsometry _ _).symm.norm_map _

end NLS.KdV
