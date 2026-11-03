import NLS.KdV.HillPhysicalIntegerActions
import NLS.Articles.KdVEstimates.IntegerEstimates

/-! # Both integer spectral estimates on actual real mean-zero periodic Sobolev representatives and arbitrary continuous realizations. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.KdVEstimates
open NLS.KdV
theorem theorem2_physical (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ a : ScalarSobolev m,
      ∀ hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential m hm a x).im = 0,
      (∫ x in (0 : ℝ)..1, hillSharedPhysicalPotential m hm a (x : AddCircle (2 : ℝ))) = 0 →
      let A := hillPhysicalSobolevActionMass m hm a hreal
      let top := hillSourceSobolevNorm m m le_rfl a
      let low := hillSourceSobolevNorm m (m-1) (by omega) a
      (A m ≤ c^2*(top^2+(1+low)^(2*m)*low^2)) ∧
      (top^2 ≤ d^2*(A m+(1+A (m-1))^m*A (m-1))) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := theorem2_native m hm
  refine ⟨c,d,hc,hd,?_⟩
  intro a hreal hmean
  let p := hillPhysicalSobolevNative m hm a hreal
  have h := hbound p (hillPhysicalSobolevNative_mean_zero m hm a hreal hmean)
  dsimp only
  rw [hillPhysicalSobolevActionMass_eq_native m hm a hreal m le_rfl,
    hillPhysicalSobolevActionMass_eq_native m hm a hreal (m-1) (by omega)]
  simpa only [hillSourceSobolevNorm,hillScalarSobolevLower_self,
    hillRealNativeIntegerLower,p,hillPhysicalSobolevNative,hillNativeIntegerLower_scalarToNative] using h

theorem theorem2_continuous (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ Q : C(AddCircle (2 : ℝ),ℂ),
      ∀ hper : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1,
      ∀ hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0,
      (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0 →
      ∀ a : ScalarSobolev m,
      (∀ k : ℤ, a.val k = periodOneCoefficient (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) k) →
      let A := hillContinuousActionMass Q hper hreal
      let top := hillSourceSobolevNorm m m le_rfl a
      let low := hillSourceSobolevNorm m (m-1) (by omega) a
      (A m ≤ c^2*(top^2+(1+low)^(2*m)*low^2)) ∧
      (top^2 ≤ d^2*(A m+(1+A (m-1))^m*A (m-1))) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := theorem2_physical m hm
  refine ⟨c,d,hc,hd,?_⟩
  intro Q hper hreal hmean a hcoeff
  have hrep := hillSharedPhysicalPotential_eq_of_coefficients m hm a Q hper hcoeff
  subst Q
  exact hbound a hreal hmean

end NLS.Articles.KdVEstimates
