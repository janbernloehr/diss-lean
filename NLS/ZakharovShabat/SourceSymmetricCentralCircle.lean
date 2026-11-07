import NLS.ZakharovShabat.SourcePsiReflectionPeriods

/-! A reflected central gap containing zero admits an ACTUAL original
period circle centered at zero. Reflecting an existing circle supplies
the second enclosure and the separation from every other actual gap. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def SourcePeriodicReflection.zeroCenteredPeriodCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ)
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ 0)
    (hzero : (0:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ 0) :
    SourceCriticalRootPeriodCircle hp hp1 ψ 0 where
  center := 0
  radius := D.radius
  radius_pos := D.radius_pos
  gap := by
    intro z hz
    have hD := D.gap hz
    let E : SourceCriticalRootPeriodCircle hp hp1 ψ 0 := h.periodCircleNeg D
    have hE := E.gap hz
    have h₁ : ‖z-(D.center:ℂ)‖ < D.radius := by simpa only [mem_ball,dist_eq_norm] using hD
    have h₂ : ‖z+(D.center:ℂ)‖ < D.radius := by
      simpa only [E,SourcePeriodicReflection.periodCircleNeg,Complex.ofReal_neg,sub_neg_eq_add,
        mem_ball,dist_eq_norm] using hE
    have ht := norm_add_le (z-(D.center:ℂ)) (z+(D.center:ℂ))
    have he : (z-(D.center:ℂ))+(z+(D.center:ℂ)) = 2*z := by ring
    rw [he,norm_mul,norm_ofNat] at ht
    simp only [Complex.ofReal_zero,mem_ball,dist_zero_right]
    linarith
  other := by
    intro m hm z hz
    have hc : |D.center| < D.radius := by
      simpa only [mem_ball,dist_eq_norm,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs] using D.gap hzero
    have hcl := (abs_lt.mp hc).1
    have hcr := (abs_lt.mp hc).2
    have h₁ := D.other m hm z hz
    let E : SourceCriticalRootPeriodCircle hp hp1 ψ 0 := h.periodCircleNeg D
    have h₂ := E.other m hm z hz
    change z.re < -D.center-D.radius ∨ -D.center+D.radius < z.re at h₂
    simp only [zero_sub,zero_add]
    by_cases hzre : 0 ≤ z.re
    · right
      have hr₁ := h₁.resolve_left (by linarith)
      have hr₂ := h₂.resolve_left (by linarith)
      linarith
    · left
      have hl₁ := h₁.resolve_right (by linarith)
      have hl₂ := h₂.resolve_right (by linarith)
      linarith

end NLS.ZakharovShabat
