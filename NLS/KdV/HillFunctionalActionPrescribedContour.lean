import NLS.KdV.HillPrescribedActionCircle

/-! Every native scalar Gardner functional pairs with an actual
action by integrating its fixed-energy discriminant brackets on the
actual cycle-labelled prescribed circle. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem functional_action_prescribed_circle (P : HillProductEquationPatch)
    (k : ℕ+) (F : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket F (hillHminusCanonicalAction k) q =
      -(2*(Real.pi:ℂ)⁻¹)*(∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
        (z/sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z)*
          NLS.Poisson.hminusGardnerBracket F
            (fun p => hillHminusDiscriminant p (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) q) := by
  let B := P.parent.parent.miuraBall.actionBall
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((k:ℕ):ℤ)
    (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hci := circleIntegrable_hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ)
    (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _).le D.sphere_subset_rootDomain
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ F q) (fderiv ℂ (hillHminusCanonicalAction k) q) = _
  rw [P.action_cotangent_prescribed_circle_of_real k q hq hr,map_smul,smul_eq_mul,
    map_circleIntegral _ hci]
  congr 1
  apply circleIntegral.integral_congr (P.radii_pos _).le
  intro z _
  simp only [hillMiuraActionCotangentIntegrand,map_smul,smul_eq_mul]
  rfl

end NLS.KdV.HillProductEquationPatch
