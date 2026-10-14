import NLS.ZakharovShabat.SourceLemma12_3
import NLS.ZakharovShabat.SourceGapFunctionalZeros
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-!
# Lemma 12.2 for numerators on arbitrary local gap neighborhoods

Divide by the nonvanishing omitted root product only where the numerator
is analytic, then apply the local mean-value theorem. The constructed
contour lies in the supplied neighborhood and original isolating disk,
avoids all periodic gaps, and has winding one.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The zero-functional implication on an admissible contour adapted to any analytic gap neighborhood. -/
theorem SourceCriticalRootPeriodCircle.lemma12_2_local
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (hmn : m ≠ n)
    (U : Set ℂ) (hU : IsOpen U) (hgapU : sourcePeriodicSegment hp hp1 ψ m ⊆ U)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U)
    (hreal : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m, (F z).im = 0) :
    ∃ Γ : PiecewiseC1Loop,
      Γ.Inside ((U ∩ ball (D.center:ℂ) D.radius) \ sourcePeriodicSegment hp hp1 ψ m) ∧
      Γ.Inside (sourceCanonicalRootDomain hp hp1 ψ) ∧
      Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) = 1 ∧
      (sourceGapFunctional hp hp1 n m ψ Γ F = 0 →
        ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m, F μ = 0) := by
  let V := U ∩ ball (D.center:ℂ) D.radius
  let P : ℂ → ℂ := sourceStandardRootOmittedProduct hp hp1 m ψ
  let g : ℂ → ℂ := fun z => F z/P z
  have hgapV : sourcePeriodicSegment hp hp1 ψ m ⊆ V := fun z hz => ⟨hgapU hz,D.gap hz⟩
  have hVdom : V ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    fun z hz => D.closedBall_subset_omittedDomain (ball_subset_closedBall hz.2)
  obtain ⟨W,_,_,hrealW,hdata⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  have hP : AnalyticOnNhd ℂ P (sourceStandardRootOmittedDomain hp hp1 ψ m) :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 m W (hdata m).2.1 ψ (hrealW hψ)
  have hg : AnalyticOnNhd ℂ g V := by
    intro z hz
    exact (hF z hz.1).div (hP z (hVdom hz))
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hVdom hz))
  have hgreal : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m, (g z).im = 0 := by
    intro z hz
    have hzIm := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hψ m z hz
    have hzReal : (z.re:ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using hzIm.symm
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := hVdom (hgapV hz)
    have hzRDom : (z.re:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := by rw [hzReal]; exact hzDom
    have hPr : (P z).im = 0 := by
      simpa only [P,hzReal] using sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis
        hp hp1 ψ hψ m z.re hzRDom
    simp [g,Complex.div_im,hreal z hz,hPr]
  obtain ⟨Γ,hin,hw,_,_,_,_,hmean⟩ := sourceLemma12_3_local hp hp1 ψ m V (hU.inter isOpen_ball) hgapV g hg
  have hrootdom : V \ sourcePeriodicSegment hp hp1 ψ m ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    intro z hz k
    by_cases hkm : k = m
    · subst k; exact hz.2
    · exact hVdom hz.1 k hkm
  refine ⟨Γ,hin,fun i t => hrootdom (hin i t),hw,?_⟩
  intro hzero
  have hnm : ((n-m:ℤ):ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  have hcanon0 : Γ.integral (fun z => F z/sourceCanonicalRoot hp hp1 ψ z) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hnm
  have hpoint : EqOn (fun z => g z/sourceStandardRoot hp hp1 ψ m z)
      (fun z => (2*Complex.I)*(F z/sourceCanonicalRoot hp hp1 ψ z))
      (V \ sourcePeriodicSegment hp hp1 ψ m) := by
    intro z hz
    have hPz := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hVdom hz.1)
    have hSz := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z hz.2
    dsimp [g,P]
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z]
    field_simp [hPz,hSz,Complex.I_ne_zero]
  have hroot0 : Γ.integral (fun z => g z/sourceStandardRoot hp hp1 ψ m z) = 0 := by
    rw [Γ.integral_congr hin hpoint,Γ.integral_const_mul,hcanon0,mul_zero]
  obtain ⟨μ,hμ,hvalue⟩ := hmean hgreal
  rw [PiecewiseC1Loop.normalizedIntegral,hroot0,mul_zero] at hvalue
  have hgzero : g μ = 0 := neg_eq_zero.mp hvalue.symm
  have hPμ : P μ ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m (hVdom (hgapV hμ))
  refine ⟨μ,hμ,?_⟩
  have he := congrArg (fun z : ℂ => z*P μ) hgzero
  simpa [g,hPμ] using he

end NLS.ZakharovShabat
