import NLS.SequenceSpaces.SobolevSignedCompletion
import NLS.SequenceSpaces.SignChange

/-! Exact half-order transport of weighted signed packets. The original
source conjugation and every fixed physical output sign are retained. -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Weight

theorem sobolev_half_transport_ratio (r : ℝ) (j : ℤ) :
    (sobolev r j:ℂ)/(sobolev (r-1/2) j:ℂ)=(sobolev (1/2) j:ℂ) := by
  conv_lhs => lhs; rw [show r=(r-1/2)+1/2 by ring,sobolev_add,Complex.ofReal_mul]
  exact mul_div_cancel_left₀ _ (complex_ne_zero _ _)

end NLS.Weight
namespace NLS.WeightedCoeff

def signedHalfTarget (v : Weight) (r : ℝ) (e : ℤ → Bool)
    (A : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev r) 2)
    (p : WeightedCoeff v 2) : WeightedCoeff (Weight.sobolev (r-1/2)) 2 :=
  signedTargetLift v (Weight.sobolev (r-1/2))
    (fun q => Coeff.signChange e (weightIsometry (Weight.sobolev r) 2 (A q))) p

theorem signedHalfTarget_apply (v : Weight) (hv : ∀ j, v (-j)=v j)
    (r : ℝ) (e : ℤ → Bool) (A : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev r) 2)
    (p : WeightedCoeff v 2) (j : ℤ) :
    (signedHalfTarget v r e A p).val j=(Weight.sobolev (1/2) j:ℂ)*
      ((if e j then -(A p).val j else (A p).val j)+
        conj (if e (-j) then -(A (conjugateReflection v hv p)).val (-j)
          else (A (conjugateReflection v hv p)).val (-j))) := by
  have hc (q : WeightedCoeff v 2) (k : ℤ) :
      Coeff.signChange e (weightIsometry (Weight.sobolev r) 2 (A q)) k=
        (Weight.sobolev r k:ℂ)*(if e k then -(A q).val k else (A q).val k) := by
    rw [Coeff.signChange_apply]
    change (if e k then -((Weight.sobolev r k:ℂ)*(A q).val k) else
      (Weight.sobolev r k:ℂ)*(A q).val k)=_
    cases e k <;> simp only [Bool.false_eq_true,↓reduceIte]
    ring
  rw [signedHalfTarget,signedTargetLift_apply,normalizedSignedCompletion_apply v hv,hc,hc,
    Weight.sobolev_neg,map_mul,Complex.conj_ofReal,←mul_add]
  rw [mul_div_right_comm,Weight.sobolev_half_transport_ratio]

theorem analyticOnNhd_signedHalfTarget (v : Weight) (hv : ∀ j, v (-j)=v j)
    (r : ℝ) (e : ℤ → Bool) (A : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev r) 2)
    (U : Set (WeightedCoeff v 2)) (hA : AnalyticOnNhd ℂ A U) :
    AnalyticOnNhd ℂ (signedHalfTarget v r e A) (U∩conjugateReflection v hv ⁻¹' U) := by
  apply analyticOnNhd_signedTargetLift v (Weight.sobolev (r-1/2)) hv _ U
  intro p hp
  exact ((Coeff.signChange e).analyticAt _).comp
    (((weightIsometry (Weight.sobolev r) 2).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp (hA p hp))

theorem norm_signedHalfTarget_le (v : Weight) (hv : ∀ j, v (-j)=v j)
    (r : ℝ) (e : ℤ → Bool) (A : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev r) 2)
    (p : WeightedCoeff v 2) (C : ℝ) (hp : ‖A p‖≤C) (hJp : ‖A (conjugateReflection v hv p)‖≤C) :
    ‖signedHalfTarget v r e A p‖≤2*C := by
  rw [signedHalfTarget,norm_signedTargetLift]
  apply norm_normalizedSignedCompletion_le v hv _ p C
  · simpa only [Coeff.norm_signChange,LinearIsometryEquiv.norm_map] using hp
  · simpa only [Coeff.norm_signChange,LinearIsometryEquiv.norm_map] using hJp

end NLS.WeightedCoeff
