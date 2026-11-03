import NLS.ZakharovShabat.SourceFullAbelianSquare
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-! # The critical period weighted by the actual Abelian square

The integral of F_k² times the discriminant derivative divided by the
canonical root is zero: the actual primitive F_k³/3 is single-valued
along the contour. This is the cancellation used in article Lemma 5.3.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted actual critical quotient is a derivative, so every
admissible closed piecewise C¹ contour has zero period. -/
theorem sourceFullAbelian_square_critical_period_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W : Set (CoeffPair p)} (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ) (k : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (sourceCanonicalRootDomain hp hp1 ψ)) :
    Γ.integral (fun z => (sourceFullAbelianPrimitive hp hp1 W k (z,ψ))^2*
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  let F : ℂ → ℂ := fun z => sourceFullAbelianPrimitive hp hp1 W k (z,ψ)
  have hF : AnalyticOnNhd ℂ F (sourceOpenGapComplement hp hp1 ψ) :=
    sourceFullAbelianPrimitive_spectral_analytic D k
  have hzero := Γ.integral_eq_zero_of_primitive
    (fun z => F z^2*deriv F z) (fun z => F z^3/3)
    (sourceOpenGapComplement hp hp1 ψ)
    ((hF.pow 2).mul hF.deriv).continuousOn (by
      intro z hz
      have hd := ((hF z hz).differentiableAt.hasDerivAt.pow 3).div_const (3:ℂ)
      have hm : (3:ℂ)*F z^2*deriv F z/3 = F z^2*deriv F z := by ring
      simpa only [Nat.reduceSub,Nat.cast_ofNat,hm] using! hd)
    (fun i u => sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hΓ i u))
  have he : Γ.integral (fun z => F z^2*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      Γ.integral (fun z => F z^2*deriv F z) := by
    apply Γ.integral_congr hΓ
    intro z hz
    dsimp only [F]
    rw [(sourceFullAbelianPrimitive_hasDerivAt D k z hz).deriv]
    rfl
  exact he.trans hzero

/-- The actual weighted critical period vanishes on every admissible circle. -/
theorem sourceFullAbelian_square_critical_circle_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W : Set (CoeffPair p)} (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ) (k : ℤ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    (∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W k (z,ψ))^2*
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  have hi : (PiecewiseC1Loop.circle c R).Inside (sourceCanonicalRootDomain hp hp1 ψ) := by
    intro i u
    apply hcircle
    change circleMap c R ((2*Real.pi)*(u:ℝ)) ∈ sphere c R
    exact circleMap_mem_sphere c hR _
  simpa only [PiecewiseC1Loop.integral_circle] using
    sourceFullAbelian_square_critical_period_eq_zero hp hp1 ψ D k (PiecewiseC1Loop.circle c R) hi

end NLS.ZakharovShabat
