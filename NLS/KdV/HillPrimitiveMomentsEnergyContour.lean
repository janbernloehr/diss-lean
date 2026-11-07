import NLS.KdV.HillPrimitiveMomentsPhysical
import NLS.KdV.HillAbelianPhysicalEnergyPullback

/-! The centered moments are literal integrals on ORIGINAL Hill energy
loops, with the canonical energy differential and exact quadratic change
of variables. No abstract moment data or replacement contour is supplied. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

def centeredEnergySquare (P : HillProductEquationPatch) (W : Set (CoeffPair 2)) (m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ)
    (Complex.sqrt (t.1+(P.parent.parent.miuraBall.actionBall.shift:ℂ)),P.sourcePsi t.2)

theorem centeredMoment_eq_original_energy_contour (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hr : IsRealPeriodOneHminusOne q) :
    P.centeredMoment W n m d q=(P.energyLoop m).integral
      (fun E => (P.centeredEnergySquare W m (E,q))^d*hillHminusCanonicalEnergyDifferential n (E,q)) := by
  let Γ := PiecewiseC1Loop.circle (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  let U := sphere (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))
  have hΓ : Γ.Inside U := by
    intro i t
    exact circleMap_mem_sphere _ (P.radii_pos (m:ℤ)).le ((2*Real.pi)*(t:ℝ))
  have he := integral_quadraticEnergyLoop Γ (P.parent.parent.miuraBall.actionBall.shift:ℂ)
    (fun E => (P.centeredEnergySquare W m (E,q))^d*hillHminusCanonicalEnergyDifferential n (E,q))
    (fun z => (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q))^d*
      P.abelianFrequencyDifferential n (z,q)) U hΓ (by
      intro z hz
      have hpos := P.positive_circle_left_of_real q hq.1 hr m
      have hb := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
      have hzr : 0<z.re := by linarith [hb.1]
      have hroot := D.sphere_subset_rootDomain hz
      rw [centeredEnergySquare,sub_add_cancel,sqrt_sq_of_re_pos z hzr,
        (P.abelianFrequencyDifferential_physical_energy_pullback q hq.1 hr z hzr hroot).2 n]
      ring)
  change (P.energyLoop m).integral _=Γ.integral _ at he
  rw [he,PiecewiseC1Loop.integral_circle]
  exact P.centeredMoment_eq_square_contour C n m d q hq

end NLS.KdV.HillProductEquationPatch
