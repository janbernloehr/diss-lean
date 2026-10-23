import NLS.ZakharovShabat.SourceDirichletSpectralSheet
import NLS.ZakharovShabat.RealGapProductSigns

/-! # Reality of the actual fixed Dirichlet spectral sheet

Every point of the fixed algebraic sheet above a real source's periodic
gap has real base and terminal coordinates. This includes both branches
and collapsed gaps, without requiring that the point is already realized
by a source flow.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both coordinates of every admissible point of a real source's fixed
Dirichlet spectral sheet are real. -/
theorem sourceDirichletSpectralSheet_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (n : ℤ) (z : ℂ × ℂ) (hz : z ∈ sourceDirichletSpectralSheet hp hp1 n φ.val) :
    z.1.im = 0 ∧ z.2.im = 0 := by
  have hμ := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ.val φ.property n z.1 hz.1
  refine ⟨hμ,?_⟩
  let Δ := canonicalDiscriminant hp (periodOnePotential φ.val) z.1
  have hcast : (z.1.re : ℂ) = z.1 := Complex.ext rfl (by simpa only [ofReal_im] using hμ.symm)
  have hreal := isRealType_periodOnePotential φ.val φ.property
  have hΔ : Δ.im = 0 := by
    change (canonicalDiscriminant hp (periodOnePotential φ.val) z.1).im = 0
    rw [← hcast]
    exact canonicalDiscriminant_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem _) hreal z.1.re
  have hge : 4 ≤ Δ.re^2 := by
    have h := discriminant_re_sq_ge_four_of_mem_canonicalGap hp hp1 _
      (periodOnePotential_mem φ.val) hreal n z.1.re
      (sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val n z.1 hz.1)
    simpa only [hcast] using h
  have hs : z.2^2 = Δ^2-4 := hz.2
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_two,mul_re,sub_re,hΔ,mul_zero,sub_zero,show (4 : ℂ).re = 4 from rfl] at hr
  simp only [pow_two,mul_im,sub_im,hΔ,mul_zero,zero_mul,zero_add,
    show (4 : ℂ).im = 0 from rfl,sub_zero] at hi
  by_cases hx : z.2.re = 0
  · nlinarith [sq_nonneg z.2.im]
  · have hprod : z.2.re*z.2.im = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_left hx

end NLS.ZakharovShabat
