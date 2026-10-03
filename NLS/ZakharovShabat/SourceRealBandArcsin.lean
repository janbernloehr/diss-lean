import NLS.ZakharovShabat.SourceCanonicalRootRealBand
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # An arcsine primitive on each real spectral band

The canonical square-root orientation identifies the actual quotient
with the derivative of a continuous arcsine expression. Its endpoint
values differ by exactly `-i*pi`, at every signed index.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous real-parameter expression for the band primitive. -/
def sourceRealBandArcsinPrimitive (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (x : ℝ) : ℂ :=
  I*(((-1 : ℝ)^n.natAbs : ℝ) : ℂ)*
    (Real.arcsin ((canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re/2) : ℂ)

theorem continuous_sourceRealBandArcsinPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) : Continuous (sourceRealBandArcsinPrimitive hp φ n) := by
  have hd : Continuous (canonicalDiscriminant hp (periodOnePotential φ)) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ)).continuousOn
  exact continuous_const.mul (continuous_ofReal.comp
    (Real.continuous_arcsin.comp ((continuous_re.comp (hd.comp continuous_ofReal)).div_const 2)))

/-- Differentiate the arcsine expression to the actual, oriented
canonical quotient on the band interior. -/
theorem hasDerivAt_sourceRealBandArcsinPrimitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 φ n) :
    HasDerivAt (sourceRealBandArcsinPrimitive hp φ n)
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) (x : ℂ) /
        sourceCanonicalRoot hp hp1 φ (x : ℂ)) x := by
  let d := (canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re
  let v := (deriv (canonicalDiscriminant hp (periodOnePotential φ)) (x : ℂ)).re
  let s : ℝ := (-1)^n.natAbs
  let a := Real.sqrt (1-(d/2)^2)
  have hsq : d^2 < 4 := sourceDiscriminant_realBand_sq_lt_four hp hp1 φ hφ n x hx
  have hlow : -1 < d/2 := by nlinarith [sq_nonneg (d+2)]
  have hhigh : d/2 < 1 := by nlinarith [sq_nonneg (d-2)]
  have ha : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  have hss : s^2 = 1 := by dsimp [s]; rw [← pow_mul]; simp [mul_comm _ 2,pow_mul]
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 from pow_ne_zero n.natAbs (by norm_num : (-1 : ℝ) ≠ 0))
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdr := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ)
    (x : ℂ) (mem_univ _)).differentiableAt.hasDerivAt.real_of_complex
  have hA := ((Real.hasDerivAt_arcsin (ne_of_gt hlow) (ne_of_lt hhigh)).comp x
    (hdr.div_const 2)).ofReal_comp.const_mul (I*(s : ℂ))
  have hderivreal : deriv (canonicalDiscriminant hp (periodOnePotential φ)) (x : ℂ) = (v : ℂ) := by
    apply Complex.ext
    · rfl
    · exact discriminant_derivative_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) x
  have hsqrt : Real.sqrt (4-d^2) = 2*a := by
    rw [show 4-d^2 = 4*(1-(d/2)^2) by ring,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1
      norm_num
    rw [hfour]
  have hroot : sourceCanonicalRoot hp hp1 φ (x : ℂ) = -I*((s*(2*a) : ℝ) : ℂ) := by
    rw [sourceCanonicalRoot_eq_signed_sqrt_on_realBand hp hp1 φ hφ n x hx]
    change -I*((s*Real.sqrt (4-d^2) : ℝ) : ℂ) = _
    rw [hsqrt]
  convert! hA using 1
  rw [hroot,hderivreal]
  change (v : ℂ)/(-I*((s*(2*a) : ℝ) : ℂ)) = I*(s : ℂ)*(((1/a)*(v/2) : ℝ) : ℂ)
  have hssc : (s : ℂ)^2 = 1 := by exact_mod_cast hss
  push_cast
  field_simp
  rw [hssc,pow_two,Complex.I_mul_I]
  ring

/-- The left endpoint of every band has the same arcsine primitive value. -/
theorem sourceRealBandArcsinPrimitive_left
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceRealBandArcsinPrimitive hp φ n
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re = I*(Real.pi : ℂ)/2 := by
  have him := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2
  have he : (((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re : ℝ) : ℂ) =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
    exact Complex.ext rfl him.symm
  have hd := (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2
  unfold sourceRealBandArcsinPrimitive
  rw [he,hd]
  by_cases hn : n % 2 = 0 <;>
    simp [neg_one_pow_eq_ite,Int.natAbs_even,Int.even_iff,hn] <;> ring

/-- The right endpoint has the opposite value, giving the band increment `-i*pi`. -/
theorem sourceRealBandArcsinPrimitive_right
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceRealBandArcsinPrimitive hp φ n
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re = -I*(Real.pi : ℂ)/2 := by
  have him := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) (n+1)).1
  have he : (((canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re : ℝ) : ℂ) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1) := by
    exact Complex.ext rfl him.symm
  have hd := (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) (n+1)).1
  unfold sourceRealBandArcsinPrimitive
  rw [he,hd]
  by_cases hn : n % 2 = 0
  · have hn' : (n+1) % 2 ≠ 0 := by omega
    simp [Int.natAbs_even,Int.even_iff,hn,hn']
    ring
  · have hn' : (n+1) % 2 = 0 := by omega
    simp [neg_one_pow_eq_ite,Int.natAbs_even,Int.even_iff,hn,hn']
    ring

end NLS.ZakharovShabat
