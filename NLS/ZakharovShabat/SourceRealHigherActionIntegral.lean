import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceRealHigherActionPositive

/-! # The literal real higher-action gap integral

The cosine substitution recovers formula (5.5) on the actual endpoint
interval. The formula includes collapsed gaps and every printed level.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Formula (5.5) with the actual discriminant arcosh profile. -/
theorem sourceRealHigherAction_eq_gapIntegral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    sourceRealHigherAction hp hp1 φ n k = (2/Real.pi) *
      ∫ x in (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
        x^k*sourceRealGapArcoshProfile hp φ.val n x := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
  let f := fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  let g := fun x => x^k*sourceRealGapArcoshProfile hp φ.val n x
  have hf : ∀ θ ∈ uIcc (0:ℝ) Real.pi, HasDerivAt f (-(b-a)/2*Real.sin θ) θ := by
    intro θ _
    have h := ((Real.hasDerivAt_cos θ).const_mul ((b-a)/2)).const_add ((a+b)/2)
    simpa only [neg_div,neg_mul,mul_neg] using! h
  have hg : ContinuousOn g (f '' uIcc (0:ℝ) Real.pi) := by
    apply ((continuous_id.pow k).continuousOn.mul (sourceRealGapArcoshProfile_spec hp hp1 φ.val φ.property n).1).mono
    rintro x ⟨θ,_,rfl⟩
    exact realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ
  have h := intervalIntegral.integral_comp_mul_deriv' hf (by fun_prop) hg
  have hf0 : f 0 = b := by dsimp [f,realGapAffinePoint,a,b]; simp only [Real.cos_zero]; ring
  have hfp : f Real.pi = a := by dsimp [f,realGapAffinePoint,a,b]; simp only [Real.cos_pi]; ring
  rw [hf0,hfp,intervalIntegral.integral_symm (a := a) (b := b)] at h
  have he : (∫ θ in (0:ℝ)..Real.pi, (g ∘ f) θ * (-(b-a)/2*Real.sin θ)) =
      -(b-a)/2 * ∫ θ in (0:ℝ)..Real.pi,
        (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^k *
          (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [f,g,sourceRealGapCosineProfile]
    ring
  rw [he] at h
  change (b-a)/Real.pi * _ = (2/Real.pi)*_
  linear_combination -(2/Real.pi)*h
/-- The original contour-defined higher action has the literal real gap integral. -/
theorem sourceIndexedHigherAction_eq_gapIntegral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 n k φ.val =
      ((2/Real.pi * ∫ x in
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
        x^k*sourceRealGapArcoshProfile hp φ.val n x : ℝ) : ℂ) := by
  rw [sourceIndexedHigherAction_eq_real hp hp1 φ,sourceRealHigherAction_eq_gapIntegral]

end NLS.ZakharovShabat
