import NLS.ZakharovShabat.SobolevHierarchyMidpointReflection
import NLS.Fourier.PeriodOneCoefficientLinear

/-! # Smooth approximation preserving either exact spatial reflection sign -/
noncomputable section
open Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

def hierarchySignedReflectionProjection (s : ℕ) (ε : ℂ) : SobolevSource s →L[ℂ] SobolevSource s :=
  (1/2:ℂ) • (ContinuousLinearMap.id ℂ _+ε • hierarchyMidpointReflection s)

theorem hierarchySignedReflectionProjection_fixed (s : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε = -1)
    (ab : SobolevSource s) (hT : hierarchyMidpointReflection s ab=ε • ab) :
    hierarchySignedReflectionProjection s ε ab=ab := by
  have hε2 : ε*ε=1 := by rcases hε with rfl | rfl <;> norm_num
  change (1/2:ℂ) • (ab+ε • hierarchyMidpointReflection s ab)=ab
  rw [hT,smul_smul,hε2,one_smul]
  module

def signedReflectedProfile (ε : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1/2:ℂ)*(f x+ε*f (1-x))

theorem contDiff_signedReflectedProfile (ε : ℂ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (signedReflectedProfile ε f) :=
  ((hf.add ((hf.comp (contDiff_const.sub contDiff_id)).const_smul ε)).const_smul (1/2:ℂ))

theorem periodic_signedReflectedProfile (ε : ℂ) (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    Function.Periodic (signedReflectedProfile ε f) 1 := by
  intro x
  unfold signedReflectedProfile
  rw [hf x,show 1-(x+1) = -x by ring,show 1-x = -x+1 by ring,hf (-x)]

theorem signedReflectedProfile_reflection (ε : ℂ) (hε : ε=1 ∨ ε = -1) (f : ℝ → ℂ) (x : ℝ) :
    ε*signedReflectedProfile ε f (1-x)=signedReflectedProfile ε f x := by
  have hε2 : ε*ε=1 := by rcases hε with rfl | rfl <;> norm_num
  unfold signedReflectedProfile
  rw [show 1-(1-x)=x by ring]
  linear_combination (f x/2)*hε2

theorem periodOneCoefficient_signedReflectedProfile (ε : ℂ) (f : ℝ → ℂ) (hf : Continuous f) (j : ℤ) :
    periodOneCoefficient (signedReflectedProfile ε f) j =
      (1/2:ℂ)*(periodOneCoefficient f j+ε*periodOneCoefficient f (-j)) := by
  unfold signedReflectedProfile
  have hc : Continuous (fun x : ℝ => ε*f (1-x)) :=
    continuous_const.mul (hf.comp (continuous_const.sub continuous_id))
  have he := periodOneCoefficient_add f (fun x : ℝ => ε*f (1-x)) hf hc j
  change periodOneCoefficient (fun x : ℝ => f x+ε*f (1-x)) j =
    periodOneCoefficient f j+periodOneCoefficient (fun x : ℝ => ε*f (1-x)) j at he
  rw [periodOneCoefficient_const_mul,he,
    periodOneCoefficient_const_mul,periodOneCoefficient_midpointReflection]

theorem hierarchySignedReflectionProjection_coefficients (s : ℕ) (ε : ℂ)
    (ab : SobolevSource s) (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (j : ℤ) :
    (hierarchySignedReflectionProjection s ε ab).1.val j =
      periodOneCoefficient (signedReflectedProfile ε a) j ∧
    (hierarchySignedReflectionProjection s ε ab).2.val j =
      periodOneCoefficient (signedReflectedProfile ε b) j := by
  constructor
  · simp [hierarchySignedReflectionProjection,hierarchyMidpointReflection_apply,
      WeightedCoeff.reflection_apply,periodOneCoefficient_signedReflectedProfile ε a ha,haq]
    ring
  · simp [hierarchySignedReflectionProjection,hierarchyMidpointReflection_apply,
      WeightedCoeff.reflection_apply,periodOneCoefficient_signedReflectedProfile ε b hb,hbq]
    ring

end NLS.ZakharovShabat
