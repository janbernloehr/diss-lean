import NLS.ZakharovShabat.ReverseCubicResonantPotential
import NLS.ZakharovShabat.SourceLemma6_7Counterexample
import NLS.ZakharovShabat.SourceLemma6_8

/-! # The reversed cubic coefficient in the original source space -/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original potential with constant first component and second mode -2n. -/
def sourceReverseCubicPotential (n : ℤ) (a b : ℂ) : CoeffPair p :=
  unitWeightedPairEquiv.symm (reverseCubicPotential SpectralWeight.one n a b)

@[simp] theorem unitWeightedPairEquiv_sourceReverseCubicPotential (n : ℤ) (a b : ℂ) :
    unitWeightedPairEquiv (sourceReverseCubicPotential (p := p) n a b) = reverseCubicPotential SpectralWeight.one n a b :=
  LinearIsometryEquiv.apply_symm_apply _ _

@[simp] theorem sourceReverseCubicPotential_fst (n : ℤ) (a b : ℂ) (k : ℤ) :
    (sourceReverseCubicPotential (p := p) n a b).fst k = if k=0 then a else 0 := by
  rw [← unitWeightedPairEquiv_fst,unitWeightedPairEquiv_sourceReverseCubicPotential,reverseCubicPotential_fst]

@[simp] theorem sourceReverseCubicPotential_snd (n : ℤ) (a b : ℂ) (k : ℤ) :
    (sourceReverseCubicPotential (p := p) n a b).snd k = if k= -(2*n) then b else 0 := by
  rw [← unitWeightedPairEquiv_snd,unitWeightedPairEquiv_sourceReverseCubicPotential,reverseCubicPotential_snd]

/-- The exact original component norms retain the two different amplitudes. -/
theorem sourceReverseCubicPotential_component_norms (n : ℤ) (a b : ℂ) :
    ‖(sourceReverseCubicPotential (p := p) n a b).fst‖ = ‖a‖ ∧
    ‖(sourceReverseCubicPotential (p := p) n a b).snd‖ = ‖b‖ := by
  have h := sourceUnitWeighted_component_norms (sourceReverseCubicPotential (p := p) n a b)
  rw [unitWeightedPairEquiv_sourceReverseCubicPotential] at h
  constructor
  · rw [← h.1]
    exact norm_weightedMode_one _ _
  · rw [← h.2]
    exact norm_weightedMode_one _ _

/-- Exact original Hilbert distance from the constant background (1,0). -/
theorem sourceReverseCubicPotential_distance_sq (n : ℤ) (b : ℂ) :
    ‖sourceReverseCubicPotential (p := 2) n 1 b - sourceConstantPotential 1 0‖^2 = ‖b‖^2 := by
  rw [← (unitWeightedPairEquiv (p := 2)).norm_map, map_sub,
    unitWeightedPairEquiv_sourceReverseCubicPotential,unitWeightedPairEquiv_sourceConstantPotential]
  exact reverseCubicPotential_distance_sq n b

/-- Every positive source cutoff removes the constant first component. -/
theorem sourceReverseCubicPotential_tail_norm_sq_le (n : ℤ) (b : ℂ) (K : ℕ) (hK : 1 ≤ K) :
    ‖sourceFourierTail K (sourceReverseCubicPotential (p := 2) n 1 b)‖^2 ≤ ‖b‖^2 := by
  rw [← (unitWeightedPairEquiv (p := 2)).norm_map,← weightedPairFourierTail_unitWeightedPairEquiv,
    unitWeightedPairEquiv_sourceReverseCubicPotential]
  exact reverseCubicPotential_tail_norm_sq_le n b K hK

/-- The actual original negative remainder at a nonzero center. -/
theorem sourceReverseCubicPotential_remainder_center (hp : p ≠ ⊤) (n : ℤ) (hn : n ≠ 0) (a b : ℂ)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv (sourceReverseCubicPotential (p := p) n a b)) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    sourceResonantBMinusFunction hp (sourceReverseCubicPotential (p := p) n a b) n ((Real.pi : ℂ)*n) -
      (sourceReverseCubicPotential (p := p) n a b).fst (-(2*n)) = a^2*b/((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2 := by
  rw [(sourceResonantFunctions_eq hp _ n _ (center_mem_resonantStrip n) h).2.2]
  simp only [sourceResonantBMinus,unitWeightedPairEquiv_sourceReverseCubicPotential] at h ⊢
  rw [reverseCubicPotential_bminus_center hp SpectralWeight.one n hn a b h]
  simp [show -(2*n) ≠ 0 by omega]

/-- Squared remainder size near the fixed background is quadratic in the perturbation. -/
theorem sourceReverseCubicPotential_remainder_norm_sq (hp : p ≠ ⊤) (n : ℤ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv (sourceReverseCubicPotential (p := p) n 1 t)) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    ‖sourceResonantBMinusFunction hp (sourceReverseCubicPotential (p := p) n 1 t) n ((Real.pi : ℂ)*n) -
      (sourceReverseCubicPotential (p := p) n 1 t).fst (-(2*n))‖^2 = t^2/(2*Real.pi*(n : ℝ))^4 := by
  rw [sourceReverseCubicPotential_remainder_center hp n hn.ne' 1 t h]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [one_pow,one_mul,norm_div,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg ht,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi*(n : ℝ))]
  ring

end NLS.ZakharovShabat
