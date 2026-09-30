import NLS.ZakharovShabat.SourceAngularBranchCosinePrimitive

/-! # The literal angular differential on analytic half-gap covers

The lifted full root is jointly analytic, including its endpoint zeros.
The literal psi/root pullback equals the regular angular numerator away
from sine zeros. Both statements use the actual half-gap branch and
assigned spectral domains at arbitrary complex sources.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem hasDerivAt_sourceAngularBranchCosinePoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (δ : CoeffPair p → ℂ) (ψ : CoeffPair p) (θ : ℂ) :
    HasDerivAt (fun e => sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ))
      (-δ ψ * Complex.sin θ) θ := by
  simpa only [sourceAngularBranchCosinePoint] using hasDerivAt_cosineGapPoint
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) (δ ψ) θ

def sourceAngularBranchCosineLiftedIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ) :
    ℂ × CoeffPair p → ℂ := fun x =>
  sourcePsiCandidate n (sourceAngularBranchCosinePoint hp hp1 m δ x,(s n x.2 : Coeff p)) /
    sourceAngularBranchCosineRoot hp hp1 m δ x * (-δ x.2 * Complex.sin x.1)

namespace SourceAngularBranchCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {δ : CoeffPair p → ℂ}
  {W V : Set (CoeffPair p)} {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

theorem analyticOnNhd_cosinePoint
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R) :
    AnalyticOnNhd ℂ (sourceAngularBranchCosinePoint hp hp1 m δ) (Ω ×ˢ V) := by
  intro x hx
  exact ((D.midpoint_analytic x.2 hx.2).comp (f := fun x : ℂ × CoeffPair p => x.2) analyticAt_snd).add
    (((D.halfGap_analytic x.2 hx.2).comp (f := fun x : ℂ × CoeffPair p => x.2) analyticAt_snd).mul
      (Complex.analyticAt_cos.comp (f := fun x : ℂ × CoeffPair p => x.1) analyticAt_fst))

theorem analyticOnNhd_cosineRoot
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R) :
    AnalyticOnNhd ℂ (sourceAngularBranchCosineRoot hp hp1 m δ) (Ω ×ˢ V) := by
  intro x hx
  have hgraph := (D.analyticOnNhd_cosinePoint x hx).prod analyticAt_snd
  have hprod := (D.omitted_analytic (sourceAngularBranchCosinePoint hp hp1 m δ x,x.2)
    ⟨D.cosine_enclosed x.2 hx.2 x.1 hx.1,hx.2⟩).comp
      (f := fun x : ℂ × CoeffPair p => (sourceAngularBranchCosinePoint hp hp1 m δ x,x.2)) hgraph
  exact ((analyticAt_const.mul ((D.halfGap_analytic x.2 hx.2).comp
    (f := fun x : ℂ × CoeffPair p => x.2) analyticAt_snd)).mul hprod).mul
      (Complex.analyticAt_sin.comp (f := fun x : ℂ × CoeffPair p => x.1) analyticAt_fst)

theorem cosineRoot_sq
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ : ℂ) (hθ : θ ∈ Ω) :
    sourceAngularBranchCosineRoot hp hp1 m δ (θ,ψ) ^ 2 =
      sourceAngularRadicand hp (sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ),ψ) :=
  sourceAngularBranchCosineRoot_sq hp hp1 m δ ψ θ (D.halfGap_sq ψ hψ)
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall (D.cosine_enclosed ψ hψ θ hθ)))

theorem cosineRoot_ne_zero
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ : ℂ) (hθ : θ ∈ Ω) (hsin : Complex.sin θ ≠ 0) :
    sourceAngularBranchCosineRoot hp hp1 m δ (θ,ψ) ≠ 0 := by
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ
    (sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ)) m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall (D.cosine_enclosed ψ hψ θ hθ)))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (D.halfGap_ne_zero ψ hψ)) hP) hsin

theorem cosineLiftedIntegrand_eq_gapNumerator
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (θ : ℂ) (hθ : θ ∈ Ω) (hsin : Complex.sin θ ≠ 0) :
    sourceAngularBranchCosineLiftedIntegrand hp hp1 n m s δ (θ,ψ) =
      (-Complex.I) * sourceAngularGapNumerator hp hp1 n m s ψ
        (sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ)) := by
  have hδ := D.halfGap_ne_zero ψ hψ
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ
    (sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ)) m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall (D.cosine_enclosed ψ hψ θ hθ)))
  dsimp only [sourceAngularBranchCosineLiftedIntegrand,sourceAngularBranchCosineRoot,sourceAngularGapNumerator]
  field_simp [hδ,hP,hsin,I_ne_zero]

end SourceAngularBranchCosineChartData
end NLS.ZakharovShabat
