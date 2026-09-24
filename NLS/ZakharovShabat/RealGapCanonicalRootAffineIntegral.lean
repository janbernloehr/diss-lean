import NLS.ZakharovShabat.RealGapCanonicalRootLowerIntegral

/-!
# Pulling real-gap integrals back to the signed affine coordinate

The coordinate `t ∈ [-1,1]` sends the standard parameter interval to
the actual periodic gap. This transfers the vanishing upper and lower
canonical-root quotient integrals to the parameter used by the straight
gap-side path construction.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Affine substitution from `[-1,1]` to `[a,b]`, with its Jacobian. -/
theorem integral_affine_gap_coordinate (a b : ℝ) (f : ℝ → ℂ) :
    (∫ t in (-1:ℝ)..1,
      ((b-a)/2) • f ((a+b)/2+(b-a)/2*t)) =
        ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_add_mul]
  congr 1 <;> ring

/-- The upper-side quotient integral vanishes after pulling it back
to the signed gap parameter. -/
theorem integral_realGapCanonicalRootUpperValue_affine_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ t in (-1:ℝ)..1,
      (((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2 : ℝ) •
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (realGapAffinePoint hp hp1 ψ n t:ℂ) /
          realGapCanonicalRootUpperValue hp hp1 ψ n
            (realGapAffinePoint hp hp1 ψ n t))) = 0 := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let f (x : ℝ) : ℂ :=
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
      realGapCanonicalRootUpperValue hp hp1 ψ n x
  change (∫ t in (-1:ℝ)..1,
    ((b-a)/2) • f ((a+b)/2+(b-a)/2*t)) = 0
  rw [integral_affine_gap_coordinate]
  exact integral_discriminant_derivative_div_realGapCanonicalRootUpperValue_eq_zero
    hp hp1 ψ hreal n hopen

/-- The analogous affine pullback of the lower-side integral vanishes. -/
theorem integral_realGapCanonicalRootLowerValue_affine_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ t in (-1:ℝ)..1,
      (((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2 : ℝ) •
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (realGapAffinePoint hp hp1 ψ n t:ℂ) /
          realGapCanonicalRootLowerValue hp hp1 ψ n
            (realGapAffinePoint hp hp1 ψ n t))) = 0 := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let f (x : ℝ) : ℂ :=
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
      realGapCanonicalRootLowerValue hp hp1 ψ n x
  change (∫ t in (-1:ℝ)..1,
    ((b-a)/2) • f ((a+b)/2+(b-a)/2*t)) = 0
  rw [integral_affine_gap_coordinate]
  exact integral_discriminant_derivative_div_realGapCanonicalRootLowerValue_eq_zero
    hp hp1 ψ hreal n hopen

end NLS.ZakharovShabat
