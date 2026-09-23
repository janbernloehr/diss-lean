import NLS.ZakharovShabat.SourcePeriodicGapTails
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Algebraic normalization of the standard periodic root

The normalized principal-square-root expression from equation (2.9)
squares to the canonical periodic endpoint factor away from the pair
midpoint. A collapsed gap reduces to the linear free-root expression.
The slit-plane and contour properties of Lemma 10.3 are subsequent steps.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized standard root with midpoint `t` and squared gap `g`. -/
def normalizedStandardRoot (t g z : ℂ) : ℂ :=
  (t-z) * Complex.sqrt (1-g/(4*(t-z)^2))

/-- Away from the midpoint, the normalized root squares to its quadratic
radicand. -/
theorem normalizedStandardRoot_sq (t g z : ℂ) (hz : t ≠ z) :
    normalizedStandardRoot t g z ^ 2 = (t-z)^2-g/4 := by
  unfold normalizedStandardRoot
  rw [mul_pow]
  have hsqrt : (Complex.sqrt (1-g/(4*(t-z)^2)))^2 =
      1-g/(4*(t-z)^2) := by
    have h := Complex.cpow_nat_inv_pow (1-g/(4*(t-z)^2)) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  rw [hsqrt]
  have htz : t-z ≠ 0 := sub_ne_zero.mpr hz
  field_simp

/-- A collapsed gap makes the standard root exactly `t-z`. -/
@[simp] theorem normalizedStandardRoot_zeroGap (t z : ℂ) :
    normalizedStandardRoot t 0 z = t-z := by
  simp [normalizedStandardRoot]

/-- Equation (2.9) with the canonical source periodic midpoint and gap. -/
def sourceStandardRoot (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  normalizedStandardRoot
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2)
    z

/-- The source standard root squares to the canonical endpoint factor
at every spectral parameter distinct from the midpoint. -/
theorem sourceStandardRoot_sq_of_ne_midpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ≠ canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) :
    sourceStandardRoot hp hp1 ψ n z ^ 2 =
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) *
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) := by
  unfold sourceStandardRoot
  rw [normalizedStandardRoot_sq _ _ _ hz.symm]
  exact (sourcePeriodicPair_factorization hp hp1 ψ n z).symm

/-- The midpoint of the canonical endpoint pair lies on its closed
straight gap segment. -/
theorem sourcePeriodicMidpoint_mem_segment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ∈ sourcePeriodicSegment hp hp1 ψ n := by
  unfold canonicalPeriodicMidpoint sourcePeriodicSegment
  convert midpoint_mem_segment (𝕜 := ℝ)
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) using 1
  rw [midpoint_eq_smul_add, invOf_eq_inv]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

/-- Outside the canonical periodic gap segment, the standard root squares
to the endpoint factor. -/
theorem sourceStandardRoot_sq_of_not_mem_segment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    sourceStandardRoot hp hp1 ψ n z ^ 2 =
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) *
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) := by
  apply sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ n z
  intro he
  exact hz (he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)

/-- A collapsed canonical periodic gap gives the linear standard root. -/
theorem sourceStandardRoot_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0) :
    sourceStandardRoot hp hp1 ψ n z =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n-z := by
  unfold sourceStandardRoot
  rw [hgap]
  simp

end NLS.ZakharovShabat
