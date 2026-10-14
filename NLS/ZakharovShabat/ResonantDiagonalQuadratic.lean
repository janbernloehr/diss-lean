import NLS.ZakharovShabat.ResonantDiagonalEstimate
import NLS.SequenceSpaces.QuasiHolderProduct

/-!
# The actual quadratic term in the resonant diagonal

The reflected pointwise product belongs to the half-exponent sequence
space. Its signed reciprocal row is exactly the leading physical
diagonal Fourier series, with the resonant denominator omitted.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
local instance resonantDiagonalQuadraticConjFact : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The reflected product of the two potential components, at exponent p/2. -/
def resonantDiagonalPairProduct (a b : Coeff p) : Coeff (p/2) := by
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  exact Coeff.quasiHolderProduct b (Coeff.reflection a)

@[simp] theorem resonantDiagonalPairProduct_apply (a b : Coeff p) (j : ℤ) :
    resonantDiagonalPairProduct a b j = b j*a (-j) := rfl

/-- Hölder gives constant one, including half-exponents below one. -/
theorem norm_resonantDiagonalPairProduct_le (hp : p ≠ ⊤) (a b : Coeff p) :
    ‖resonantDiagonalPairProduct a b‖ ≤ ‖a‖*‖b‖ := by
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  have hp0 := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  simpa [resonantDiagonalPairProduct,mul_comm] using
    Coeff.norm_quasiHolderProduct_le hp0 hp0 b (Coeff.reflection a)

/-- The leading diagonal row in physical Fourier indices. -/
def resonantDiagonalQuadratic (a b : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  ∑' j : ℤ, if j = 2*n then 0 else b j*a (-j)/(z+(Real.pi:ℂ)*n-(Real.pi:ℂ)*j)

omit [Fact (1 ≤ p)] in
/-- Reindexing identifies the quadratic row with the actual first resolvent iterate. -/
theorem resonantDiagonalQuadratic_eq_physical (a b : Coeff p) (n : ℤ) (z : ℂ) :
    resonantDiagonalQuadratic a b n z =
      ∑' k : ℤ, b (n-k)*complementarySymbol n z (-k)*a (k-n) := by
  unfold resonantDiagonalQuadratic
  rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro k
  simp only [Equiv.subLeft_apply]
  by_cases hk : -k = n
  · have he : n-k = 2*n := by omega
    simp [hk,he,complementarySymbol]
  · have he : n-k ≠ 2*n := by omega
    rw [if_neg he]
    simp only [complementarySymbol,if_neg hk]
    rw [show -(n-k) = k-n by ring]
    have hd : z+(Real.pi:ℂ)*n-(Real.pi:ℂ)*((n-k:ℤ):ℂ) = z-(Real.pi:ℂ)*(-k) := by push_cast; ring
    rw [hd,div_eq_mul_inv]
    push_cast
    ring

end NLS.ZakharovShabat
