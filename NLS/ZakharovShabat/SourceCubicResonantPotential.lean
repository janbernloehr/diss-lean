import NLS.ZakharovShabat.CubicResonantPotential
import NLS.ZakharovShabat.SourceLemma6_8

/-! # The cubic coefficient in the original period-two source space -/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original potential with first mode 2n and second mode zero. -/
def sourceCubicPotential (n : ℤ) (a b : ℂ) : CoeffPair p :=
  unitWeightedPairEquiv.symm (cubicPotential SpectralWeight.one n a b)

@[simp] theorem unitWeightedPairEquiv_sourceCubicPotential (n : ℤ) (a b : ℂ) :
    unitWeightedPairEquiv (sourceCubicPotential (p := p) n a b) = cubicPotential SpectralWeight.one n a b :=
  LinearIsometryEquiv.apply_symm_apply _ _

@[simp] theorem sourceCubicPotential_fst (n : ℤ) (a b : ℂ) (k : ℤ) :
    (sourceCubicPotential (p := p) n a b).fst k = if k=2*n then a else 0 := by
  rw [← unitWeightedPairEquiv_fst,unitWeightedPairEquiv_sourceCubicPotential,cubicPotential_fst]

@[simp] theorem sourceCubicPotential_snd (n : ℤ) (a b : ℂ) (k : ℤ) :
    (sourceCubicPotential (p := p) n a b).snd k = if k=0 then b else 0 := by
  rw [← unitWeightedPairEquiv_snd,unitWeightedPairEquiv_sourceCubicPotential,cubicPotential_snd]

/-- Exact original Hilbert pair norm. -/
theorem sourceCubicPotential_norm_sq (n : ℤ) (a b : ℂ) :
    ‖sourceCubicPotential (p := 2) n a b‖^2 = ‖a‖^2+‖b‖^2 := by
  simpa only [sourceCubicPotential,LinearIsometryEquiv.norm_map] using cubicPotential_norm_sq n a b

/-- The actual original analytic remainder at the free center. -/
theorem sourceCubicPotential_remainder_center (hp : p ≠ ⊤) (n : ℤ) (hn : n ≠ 0) (a b : ℂ)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv (sourceCubicPotential (p := p) n a b)) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    sourceResonantBPlusFunction hp (sourceCubicPotential (p := p) n a b) n ((Real.pi : ℂ)*n) -
      (sourceCubicPotential (p := p) n a b).snd (2*n) = a*b^2/((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2 := by
  rw [(sourceResonantFunctions_eq hp _ n _ (center_mem_resonantStrip n) h).2.1]
  simp only [sourceResonantBPlus,unitWeightedPairEquiv_sourceCubicPotential] at h ⊢
  rw [cubicPotential_bplus_center hp SpectralWeight.one n hn a b h]
  simp [show 2*n ≠ 0 by omega]

/-- Positive equal amplitudes give an exactly cubic remainder norm. -/
theorem sourceCubicPotential_remainder_norm (hp : p ≠ ⊤) (n : ℤ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv (sourceCubicPotential (p := p) n t t)) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    ‖sourceResonantBPlusFunction hp (sourceCubicPotential (p := p) n t t) n ((Real.pi : ℂ)*n) -
      (sourceCubicPotential (p := p) n t t).snd (2*n)‖ = t^3/(2*Real.pi*(n : ℝ))^2 := by
  rw [sourceCubicPotential_remainder_center hp n hn.ne' t t h,norm_div,norm_mul,norm_pow,norm_pow]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Complex.norm_real,Real.norm_of_nonneg ht,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi*(n : ℝ))]
  ring

end NLS.ZakharovShabat
