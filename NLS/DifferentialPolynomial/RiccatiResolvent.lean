import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The universal differential-algebra Riccati resolvent identities

Two oppositely directed Riccati series produce both gradient components and
the scalar coupling term of the all-order Lenard recurrence.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem derivation_inverse_of_mul_eq_one (D : Derivation K A A) (u v : A)
    (hu : u*v = 1) : D v = -v^2*D u := by
  have hd := congrArg D hu
  simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at hd
  linear_combination v*hd - D v*hu

/-- The three resolvent components satisfy the coupled Lenard identities.
The inverse and the two Riccati solutions are explicit algebraic inputs;
their formal-series construction is independent of this universal identity. -/
theorem riccati_resolvent_identities (D : Derivation K A A) (t a b r s v : A)
    (ht : D t = 0)
    (hr : r = -b+t*D r+a*t^2*r^2)
    (hs : s = -a-t*D s+b*t^2*s^2)
    (hv : (1+t^2*r*s)*v = 1) :
    r*v = -b+t*D (r*v)+2*b*t*(t*r*s*v) ∧
      s*v = -a-t*D (s*v)+2*a*t*(t*r*s*v) ∧
      D (t*r*s*v) = b*(s*v)-a*(r*v) := by
  let u := 1+t^2*r*s
  have huv : u*v = 1 := hv
  have hdv := derivation_inverse_of_mul_eq_one D u v huv
  have hdu : D u = t^2*(D r*s+r*D s) := by
    simp [u, Derivation.leibniz, smul_eq_mul, ht]
    ring
  rw [hdu] at hdv
  have htdv : t*D v = -t^2*v*(b*s-a*r) := by
    linear_combination t*hdv + t^2*v^2*s*hr - t^2*v^2*r*hs +
      -(t^2*v*(b*s-a*r))*hv
  have hd1 : D (r*v) = r*D v+v*D r := by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hd2 : D (s*v) = s*D v+v*D s := by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hd3 : D (t*r*s*v) = t*(D r*s*v+r*D s*v+r*s*D v) := by
    simp [Derivation.leibniz, smul_eq_mul, ht]
    ring
  constructor
  · rw [hd1]
    linear_combination v*hr - r*htdv - b*hv
  constructor
  · rw [hd2]
    linear_combination v*hs + s*htdv - a*hv
  · rw [hd3]
    linear_combination -s*v*hr + r*v*hs + r*s*htdv

/-- The resolvent components are variational coefficients modulo an explicit
total derivative. Here w is the linearized Riccati solution for perturbations
h and k of the two fields. Integrating a periodic coefficient kills precisely
the displayed derivative term. -/
theorem riccati_resolvent_variation_identity (D : Derivation K A A)
    (t a b r s v h k w : A) (ht : D t = 0)
    (hr : r = -b+t*D r+a*t^2*r^2)
    (hs : s = -a-t*D s+b*t^2*s^2)
    (hv : (1+t^2*r*s)*v = 1)
    (hw : w = -k+t*D w+h*t^2*r^2+2*a*t^2*r*w) :
    h*r+a*w = h*(r*v)+k*(s*v)-D (t*(s*v)*w) := by
  have hB := (riccati_resolvent_identities D t a b r s v ht hr hs hv).2.1
  have hA : r-t^2*(s*v)*r^2 = r*v := by linear_combination -r*hv
  have hd : D (t*(s*v)*w) = t*(s*v)*D w+t*w*D (s*v) := by
    simp [Derivation.leibniz, smul_eq_mul, ht]
    ring
  rw [hd]
  linear_combination -(s*v)*hw + w*hB + h*hA

end NLS.DifferentialPolynomial
