import NLS.ZakharovShabat.DeletedSpectralPairProducts
import NLS.ZakharovShabat.PeriodicEndpointProducts
import NLS.ZakharovShabat.CanonicalCriticalPoints
import NLS.ComplexAnalysis.QuadraticCriticalIdentity

/-!
# The quadratic gap factor of the discriminant

Deleting one canonical endpoint pair defines the entire remaining product.
The factorization uses `-4`, as forced by the free discriminant. Its derivative
at a critical point isolates the squared gap without assuming the gap is open.
These are the exact identities underlying Lemma 8.6, before its lp estimates.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The midpoint of the canonical periodic endpoint pair. -/
def canonicalPeriodicMidpoint (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ :=
  (canonicalPeriodicLeft hp hp1 φ heven n+canonicalPeriodicRight hp hp1 φ heven n)/2

/-- The oriented difference of the canonical periodic endpoints. -/
def canonicalPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ :=
  canonicalPeriodicRight hp hp1 φ heven n-canonicalPeriodicLeft hp hp1 φ heven n

/-- The remaining entire product after removing the nth canonical pair. -/
def canonicalDeletedPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ → ℂ :=
  deletedSpectralPairProduct (canonicalPeriodicLeft hp hp1 φ heven)
    (canonicalPeriodicRight hp hp1 φ heven) n

/-- The remaining canonical product is entire for all even complex potentials. -/
theorem analyticOnNhd_canonicalDeletedPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) :
    AnalyticOnNhd ℂ (canonicalDeletedPeriodicProduct hp hp1 φ heven n) univ :=
  analyticOnNhd_deletedSpectralPairProduct hp _ _
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.left_displacement
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.right_displacement n

/-- The discriminant's characteristic function factors by any canonical pair, at every spectral point. -/
theorem canonicalDiscriminant_sq_sub_four_eq_pair_mul (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) (z : ℂ) :
    (canonicalDiscriminant hp φ z)^2-4 =
      (-4*(canonicalPeriodicLeft hp hp1 φ heven n-z)*(canonicalPeriodicRight hp hp1 φ heven n-z))*
        canonicalDeletedPeriodicProduct hp hp1 φ heven n z := by
  rw [← canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ heven z,
    ← canonicalPeriodicEndpoints_product hp hp1 φ heven]
  exact entireSpectralPairProduct_eq_deleted hp _ _
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.left_displacement
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.right_displacement n z

/-- The corrected midpoint and squared-gap factorization used in Lemma 8.6. -/
theorem canonicalDiscriminant_sq_sub_four_eq_midpoint_mul (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) (z : ℂ) :
    (canonicalDiscriminant hp φ z)^2-4 =
      -4*((z-canonicalPeriodicMidpoint hp hp1 φ heven n)^2-(canonicalPeriodicGap hp hp1 φ heven n)^2/4)*
        canonicalDeletedPeriodicProduct hp hp1 φ heven n z := by
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 φ heven n z]
  unfold canonicalPeriodicMidpoint canonicalPeriodicGap
  ring

/-- Differentiation at any discriminant critical point gives the exact quadratic identity. -/
theorem discriminant_critical_midpoint_identity (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) (c : ℂ)
    (hc : deriv (canonicalDiscriminant hp φ) c = 0) :
    2*(c-canonicalPeriodicMidpoint hp hp1 φ heven n)*canonicalDeletedPeriodicProduct hp hp1 φ heven n c+
      ((c-canonicalPeriodicMidpoint hp hp1 φ heven n)^2-(canonicalPeriodicGap hp hp1 φ heven n)^2/4)*
        deriv (canonicalDeletedPeriodicProduct hp hp1 φ heven n) c = 0 :=
  NLS.ComplexAnalysis.quadratic_factor_critical_identity _ _ _ _ c
    ((analyticOnNhd_canonicalDiscriminant hp hp1 φ heven c (mem_univ _)).differentiableAt)
    ((analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 φ heven n c (mem_univ _)).differentiableAt)
    (canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 φ heven n) hc

/-- At the indexed critical point, the coefficient times its midpoint offset contains the squared gap. -/
theorem canonicalCriticalPoints_midpoint_offset_identity (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) :
    let c := canonicalCriticalPoints hp hp1 φ heven n
    let a := c-canonicalPeriodicMidpoint hp hp1 φ heven n
    let G := canonicalDeletedPeriodicProduct hp hp1 φ heven n
    (2*G c+a*deriv G c)*a = (canonicalPeriodicGap hp hp1 φ heven n)^2*(deriv G c/4) := by
  apply NLS.ComplexAnalysis.quadratic_critical_offset_identity
  exact discriminant_critical_midpoint_identity hp hp1 φ heven n _
    (canonicalCriticalPoints_is_critical hp hp1 φ heven n)

/-- The exact solved offset formula needs only a nonzero coefficient, even for a collapsed gap. -/
theorem canonicalCriticalPoints_midpoint_offset_eq (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ)
    (hne : 2*canonicalDeletedPeriodicProduct hp hp1 φ heven n (canonicalCriticalPoints hp hp1 φ heven n)+
      (canonicalCriticalPoints hp hp1 φ heven n-canonicalPeriodicMidpoint hp hp1 φ heven n)*
        deriv (canonicalDeletedPeriodicProduct hp hp1 φ heven n) (canonicalCriticalPoints hp hp1 φ heven n) ≠ 0) :
    let c := canonicalCriticalPoints hp hp1 φ heven n
    let a := c-canonicalPeriodicMidpoint hp hp1 φ heven n
    let G := canonicalDeletedPeriodicProduct hp hp1 φ heven n
    a = (canonicalPeriodicGap hp hp1 φ heven n)^2*(deriv G c/(4*(2*G c+a*deriv G c))) := by
  apply NLS.ComplexAnalysis.quadratic_critical_offset_eq _ _ _ _ _ hne
  exact discriminant_critical_midpoint_identity hp hp1 φ heven n _
    (canonicalCriticalPoints_is_critical hp hp1 φ heven n)

end NLS.ZakharovShabat
