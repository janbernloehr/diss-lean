import NLS.ZakharovShabat.RealGapCanonicalRootSign

/-!
# Canonical-root boundary values in real spectral coordinates

The inverse affine gap coordinate identifies interior real spectral
points with parameters in `(-1, 1)`. It transports the constant-sign
canonical-root boundary identity to the interval between the actual
periodic endpoints.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inverse of the real affine canonical-gap coordinate. -/
def realGapInverseCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (x : ℝ) : ℝ :=
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  (2*x-a-b)/(b-a)

/-- The canonical-root upper-side value indexed by a real spectral
point in an open gap. -/
def realGapCanonicalRootUpperValue (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (x : ℝ) : ℂ :=
  sourceCanonicalRootGapUpperValue hp hp1 ψ n
    (realGapInverseCoordinate hp hp1 ψ n x)

/-- Interior real spectral points have inverse parameter in `(-1,1)`. -/
theorem realGapInverseCoordinate_mem_Ioo
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    realGapInverseCoordinate hp hp1 ψ n x ∈ Ioo (-1) 1 := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  change a < x ∧ x < b at hx
  have hab : 0 < b-a := by linarith
  change -1 < (2*x-a-b)/(b-a) ∧
    (2*x-a-b)/(b-a) < 1
  constructor
  · rw [lt_div_iff₀ hab]
    linarith [hx.1]
  · rw [div_lt_iff₀ hab]
    linarith [hx.2]

/-- The affine coordinate followed by its inverse is the identity
on a nondegenerate real gap. -/
theorem realGapAffinePoint_inverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (x : ℝ) :
    realGapAffinePoint hp hp1 ψ n
      (realGapInverseCoordinate hp hp1 ψ n x) = x := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  have hne : b-a ≠ 0 := by
    change a < b at hopen
    linarith
  change (a+b)/2 + (b-a)/2 * ((2*x-a-b)/(b-a)) = x
  field_simp
  nlinarith [hne]

/-- The upper canonical-root boundary value has a fixed sign relative
to the positive arcosh square root over the actual real spectral gap. -/
theorem realGapCanonicalRootUpperValue_eq_or_eq_neg_two_sqrt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∀ x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re,
      realGapCanonicalRootUpperValue hp hp1 ψ n x =
        ((2*Real.sqrt ((realGapHalfDiscriminant hp
          (periodOnePotential ψ) n x)^2-1):ℝ):ℂ)) ∨
    (∀ x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re,
      realGapCanonicalRootUpperValue hp hp1 ψ n x =
        -((2*Real.sqrt ((realGapHalfDiscriminant hp
          (periodOnePotential ψ) n x)^2-1):ℝ):ℂ)) := by
  obtain hsign | hsign :=
    sourceCanonicalRootGapUpperValue_eq_or_eq_neg_two_sqrt
      hp hp1 ψ hreal n hopen
  · left
    intro x hx
    have ht := realGapInverseCoordinate_mem_Ioo hp hp1 ψ n hx
    unfold realGapCanonicalRootUpperValue
    rw [hsign _ ht, realGapAffinePoint_inverse hp hp1 ψ n hopen x]
  · right
    intro x hx
    have ht := realGapInverseCoordinate_mem_Ioo hp hp1 ψ n hx
    unfold realGapCanonicalRootUpperValue
    rw [hsign _ ht, realGapAffinePoint_inverse hp hp1 ψ n hopen x]

end NLS.ZakharovShabat
