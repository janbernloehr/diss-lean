import NLS.DifferentialPolynomial.EulerLagrange
import NLS.DifferentialPolynomial.JetOrderBounds

/-! # Sharp total-derivative bounds for Euler derivatives

Partial differentiation removes the selected jet's derivative weight. The
spatial derivatives in the Euler operator restore exactly that weight.
Consequently taking a variational gradient never increases the total number
of derivatives in a monomial.
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

namespace Supported
theorem pderiv {P Q : Monomial → Prop} {p : Polynomial} (hp : Supported P p) (v : Jet)
    (h : ∀ m, P m → m v ≠ 0 → Q (m-Finsupp.single v 1)) :
    Supported Q (MvPolynomial.pderiv v p) := by
  classical
  conv => arg 2; rw [p.as_sum]
  rw [map_sum]
  apply Supported.sum
  intro m hm
  rw [MvPolynomial.pderiv_monomial]
  by_cases hv : m v = 0
  · simp only [hv, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
    exact Supported.zero
  · exact Supported.monomial _ _ (h m (hp m hm) hv)
end Supported

namespace DerivativeOrderLE
variable {p : Polynomial} {d : ℤ}

theorem C (c : ℂ) : DerivativeOrderLE (MvPolynomial.C c) 0 := by
  change Supported _ (MvPolynomial.monomial 0 c)
  exact Supported.monomial _ _ (by simp)

theorem pderiv (hp : DerivativeOrderLE p d) (v : Jet) :
    DerivativeOrderLE (MvPolynomial.pderiv v p) (d-(v.2 : ℤ)) :=
  Supported.pderiv hp v (fun m hm hv => by
    rw [weight_erase_one _ m v (Finsupp.mem_support_iff.mpr hv)]
    exact sub_le_sub_right hm _)

theorem iterate_spatialDerivative (hp : DerivativeOrderLE p d) (n : ℕ) :
    DerivativeOrderLE (((DifferentialPolynomial.spatialDerivative : Polynomial → Polynomial)^[n]) p) (d+n) := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    convert ih.spatialDerivative using 1
    push_cast
    ring

/-- The Euler operator preserves the total-derivative bound at every order. -/
theorem eulerDerivative (hp : DerivativeOrderLE p d) (field : Bool) :
    DerivativeOrderLE (DifferentialPolynomial.eulerDerivative field p) d := by
  unfold DifferentialPolynomial.eulerDerivative
  apply DerivativeOrderLE.sum
  intro v _
  split_ifs
  · convert (DerivativeOrderLE.C ((-1 : ℂ)^v.2)).mul
      ((hp.pderiv v).iterate_spatialDerivative v.2) using 1
    ring
  · exact DerivativeOrderLE.zero _
end DerivativeOrderLE

/-- Removing a jet of maximal allowed order leaves only zero-order factors.
This is the key endpoint product estimate: there is at most one top L² jet. -/
theorem derivativeWeight_erase_top (m : Monomial) (s : ℕ) (v : Jet)
    (hm : Finsupp.weight derivativeWeight m ≤ s) (hv : v ∈ m.support) (hvs : v.2 = s) :
    Finsupp.weight derivativeWeight (m-Finsupp.single v 1) ≤ 0 := by
  rw [weight_erase_one _ m v hv]
  simp only [derivativeWeight, hvs]
  omega

end NLS.DifferentialPolynomial
