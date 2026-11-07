import NLS.KdV.HillFixedActionGradientContour

/-! A fixed actual action cotangent circle yields the Dirichlet
bracket identity at every complex source where it is valid. The
filled quotient has no moving-energy pole or gap division. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

theorem action_Dirichlet_bracket_of_cotangent_contour (B : HillHminusMiuraActionBall)
    (k m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (hcircle : sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (B.diracSource q))
    (hgradient : fderiv ℂ (hillHminusCanonicalAction k) q = -(2*(Real.pi:ℂ)⁻¹) •
      (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ) z)) :
    deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)*
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction k) (hillHminusCanonicalDirichlet m) q =
      hillHminusDirichletSheet m q*(Real.pi:ℂ)⁻¹*
        (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ) z) := by
  have hci := circleIntegrable_hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ) a R hR.le hcircle
  have hpoint (h : PeriodOneHminusOne) : (fderiv ℂ (hillHminusCanonicalAction k) q) h =
      -(2*(Real.pi:ℂ)⁻¹)*(∮ z in C(a,R), z*hillHminusDiscriminantCotangent
        (z^2-(B.shift:ℂ)) q h/sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z) := by
    rw [hgradient]
    simp only [smul_apply,smul_eq_mul]
    have hev := NLS.ComplexAnalysis.map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h) hci
    change (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ) z) h = _ at hev
    rw [hev]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro z _
    change (z/sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z)*
      hillHminusDiscriminantCotangent (z^2-(B.shift:ℂ)) q h = _
    ring
  have hb : NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction k) (hillHminusCanonicalDirichlet m) q =
      -(2*(Real.pi:ℂ)⁻¹)*(∮ z in C(a,R), z*
        NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p (z^2-(B.shift:ℂ)))
          (hillHminusCanonicalDirichlet m) q /
            sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z) := by
    rw [← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,hpoint]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only [hillHminusDiscriminantCotangent]
    rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  have hi : (2*deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q))*
      (∮ z in C(a,R), z*
        NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p (z^2-(B.shift:ℂ)))
          (hillHminusCanonicalDirichlet m) q /
            sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z) =
      -hillHminusDirichletSheet m q*
        (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ) z) := by
    rw [← circleIntegral.integral_const_mul,← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only [hillMiuraActionDirichletIntegrand,diracSource]
    linear_combination (z/sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal (B.lift q)) z)*
      hillHminus_filled_discriminant_Dirichlet_Gardner m q hq (z^2-(B.shift:ℂ))
  linear_combination deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)*hb-(Real.pi:ℂ)⁻¹*hi

end NLS.KdV.HillHminusMiuraActionBall
