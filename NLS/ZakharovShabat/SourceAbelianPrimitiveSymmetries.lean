import NLS.ZakharovShabat.SourcePrimitiveJointCovariance
import NLS.ZakharovShabat.SourceGapSymmetries
import NLS.ZakharovShabat.SourceSymmetryCore

/-! # Actual full primitive values under P, T and circle rotations -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceSignedJointMap (ε : ℂ) (A : CoeffPair p →L[ℂ] CoeffPair p) :
    (ℂ × CoeffPair p) →L[ℂ] (ℂ × CoeffPair p) :=
  (ε • ContinuousLinearMap.id ℂ ℂ).prodMap A

@[simp] theorem sourceSignedJointMap_apply (ε : ℂ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (t : ℂ × CoeffPair p) : sourceSignedJointMap ε A t = (ε*t.1,A t.2) := rfl

namespace SourceFullAbelianDifferentialData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {A V : Set (CoeffPair p)}
variable (D : SourceFullAbelianDifferentialData hp hp1 A V) (hV : IsConnected V)
include D hV

theorem primitive_componentSwap (hP : MapsTo sourceComponentSwap V V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceFullAbelianPrimitive hp hp1 A 0 (-z,sourceComponentSwap φ) =
      -sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) := by
  let B : (ℂ × CoeffPair p) →L[ℂ] (ℂ × CoeffPair p) := sourceSignedJointMap (-1) sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap
  have hb : MapsTo B (sourceCanonicalRootJointDomain hp hp1 V) (sourceCanonicalRootJointDomain hp hp1 V) := by
    intro t ht
    change sourceComponentSwap t.2 ∈ V ∧ -1*t.1 ∈ sourceCanonicalRootDomain hp hp1 (sourceComponentSwap t.2)
    exact ⟨hP ht.1,by simpa only [neg_one_mul] using (sourceCanonicalRootDomain_componentSwap hp hp1 t.2 t.1).mpr ht.2⟩
  have hd (t : ℂ × CoeffPair p) :
      canonicalDiscriminant hp (periodOnePotential (B t).2) (B t).1 =
        canonicalDiscriminant hp (periodOnePotential t.2) t.1 := by
    change canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap t.2)) (-1*t.1) = _
    simpa only [neg_one_mul] using sourceDiscriminant_componentSwap hp hp1 t.2 t.1
  have hr (t : ℂ × CoeffPair p) :
      sourceCanonicalRoot hp hp1 (B t).2 (B t).1 = -1*sourceCanonicalRoot hp hp1 t.2 t.1 := by
    change sourceCanonicalRoot hp hp1 (sourceComponentSwap t.2) (-1*t.1) = -1*_
    simpa only [neg_one_mul] using sourceCanonicalRoot_componentSwap hp hp1 t.2 t.1
  have h := D.primitive_covariance hV B (-1) (by norm_num) hb hd hr
    (fun w => by simp [B]) (z,φ) ⟨hφ,hz⟩
  change sourceFullAbelianPrimitive hp hp1 A 0 (-1*z,sourceComponentSwap φ) =
    -1*sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) at h
  simpa only [neg_one_mul] using h

theorem primitive_midpointReflection (hT : MapsTo sourceMidpointReflection V V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceFullAbelianPrimitive hp hp1 A 0 (-z,sourceMidpointReflection φ) =
      -sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) := by
  let B : (ℂ × CoeffPair p) →L[ℂ] (ℂ × CoeffPair p) := sourceSignedJointMap (-1) sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap
  have hb : MapsTo B (sourceCanonicalRootJointDomain hp hp1 V) (sourceCanonicalRootJointDomain hp hp1 V) := by
    intro t ht
    change sourceMidpointReflection t.2 ∈ V ∧ -1*t.1 ∈ sourceCanonicalRootDomain hp hp1 (sourceMidpointReflection t.2)
    exact ⟨hT ht.1,by simpa only [neg_one_mul] using (sourceCanonicalRootDomain_midpointReflection hp hp1 t.2 t.1).mpr ht.2⟩
  have hd (t : ℂ × CoeffPair p) :
      canonicalDiscriminant hp (periodOnePotential (B t).2) (B t).1 =
        canonicalDiscriminant hp (periodOnePotential t.2) t.1 := by
    change canonicalDiscriminant hp (periodOnePotential (sourceMidpointReflection t.2)) (-1*t.1) = _
    simpa only [neg_one_mul] using sourceDiscriminant_midpointReflection hp hp1 t.2 t.1
  have hr (t : ℂ × CoeffPair p) :
      sourceCanonicalRoot hp hp1 (B t).2 (B t).1 = -1*sourceCanonicalRoot hp hp1 t.2 t.1 := by
    change sourceCanonicalRoot hp hp1 (sourceMidpointReflection t.2) (-1*t.1) = -1*_
    simpa only [neg_one_mul] using sourceCanonicalRoot_midpointReflection hp hp1 t.2 t.1
  have h := D.primitive_covariance hV B (-1) (by norm_num) hb hd hr
    (fun w => by simp [B]) (z,φ) ⟨hφ,hz⟩
  change sourceFullAbelianPrimitive hp hp1 A 0 (-1*z,sourceMidpointReflection φ) =
    -1*sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) at h
  simpa only [neg_one_mul] using h

theorem primitive_circleRotation (c : Circle) (hR : MapsTo (sourceCircleRotation c) V V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceFullAbelianPrimitive hp hp1 A 0 (z,sourceCircleRotation c φ) =
      sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) := by
  have hc : (c:ℂ) ≠ 0 := by
    intro h
    have hn := Circle.norm_coe c
    rw [h,norm_zero] at hn
    norm_num at hn
  let B : (ℂ × CoeffPair p) →L[ℂ] (ℂ × CoeffPair p) := sourceSignedJointMap 1 (sourceReciprocalScaling (c:ℂ))
  have hb : MapsTo B (sourceCanonicalRootJointDomain hp hp1 V) (sourceCanonicalRootJointDomain hp hp1 V) := by
    intro t ht
    change sourceCircleRotation c t.2 ∈ V ∧ 1*t.1 ∈ sourceCanonicalRootDomain hp hp1 (sourceReciprocalScaling (c:ℂ) t.2)
    exact ⟨hR ht.1,by simpa only [one_mul,sourceCanonicalRootDomain_reciprocalScaling hp hp1 _ hc] using ht.2⟩
  have hd (t : ℂ × CoeffPair p) :
      canonicalDiscriminant hp (periodOnePotential (B t).2) (B t).1 =
        canonicalDiscriminant hp (periodOnePotential t.2) t.1 := by
    simpa only [B,sourceSignedJointMap_apply,one_mul] using sourceDiscriminant_reciprocalScaling hp hp1 _ hc t.2 t.1
  have hr (t : ℂ × CoeffPair p) :
      sourceCanonicalRoot hp hp1 (B t).2 (B t).1 = 1*sourceCanonicalRoot hp hp1 t.2 t.1 := by
    simpa only [B,sourceSignedJointMap_apply,one_mul] using sourceCanonicalRoot_reciprocalScaling hp hp1 _ hc t.2 t.1
  have h := D.primitive_covariance hV B 1 (by norm_num) hb hd hr
    (fun w => by simp [B]) (z,φ) ⟨hφ,hz⟩
  change sourceFullAbelianPrimitive hp hp1 A 0 (z,sourceReciprocalScaling (c:ℂ) φ) = _
  simpa only [B,sourceSignedJointMap_apply,one_mul] using h

end SourceFullAbelianDifferentialData
end NLS.ZakharovShabat
