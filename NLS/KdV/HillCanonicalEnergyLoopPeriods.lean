import NLS.KdV.HillPositivePatchCircles

/-! ACTUAL fixed energy loops for every positive original gap. Each
loop has winding one at the real reference source, and ONE complex
source radius preserves its canonical sheet and EXACT one-over-two-pi
Kronecker periods BEFORE ALL numerator indices. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def energyLoop (P : HillProductEquationPatch) (m : ℕ+) : PiecewiseC1Loop :=
  quadraticEnergyLoop (PiecewiseC1Loop.circle (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)))
    (P.parent.parent.miuraBall.actionBall.shift:ℂ)

theorem energyLoop_inside_local (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hpos : 0 < P.centers ((m:ℕ):ℤ)-P.radii ((m:ℕ):ℤ)) :
    (P.energyLoop m).Inside {E | (E,q) ∈ P.parent.parent.energyDomain P.parent.family} := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact P.parent.parent.energyCircle_inside P.parent.family q (P.parent.subset (P.subset hq)) m D hpos

theorem energyLoop_local_period (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hpos : 0 < P.centers ((m:ℕ):ℤ)-P.radii ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(P.energyLoop m).integral
      (fun E => P.parent.parent.energyDifferential P.parent.family n (E,q)) = if m = n then 1 else 0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact P.parent.parent.energyDifferential_circle_period P.parent.family q (P.parent.subset (P.subset hq)) n m D hpos

theorem energyLoop_winding_one_of_real (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    (P.energyLoop m).windingIntegral ((sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))^2-
      (P.parent.parent.miuraBall.actionBall.shift:ℂ)) = 1 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact winding_one_miura_action_contour (P.parent.parent.miuraBall.actionBall.lift q)
    (P.parent.parent.miuraBall.actionBall.shift:ℂ) ((m:ℕ):ℤ) D (P.positive_circle_left_of_real q hq hr m)

theorem exists_canonical_energyLoop_complex_period_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ hillHminusEnergySheetSource ∧
      ∀ y ∈ ball q r, (P.energyLoop m).Inside {E | (E,y) ∈ hillHminusCanonicalEnergyRootDomain} ∧
        ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*(P.energyLoop m).integral
          (fun E => hillHminusCanonicalEnergyDifferential n (E,y)) = if m = n then 1 else 0 := by
  have hpos := P.positive_circle_left_of_real q hq hr m
  obtain ⟨rG,hrG,htransport⟩ := exists_uniform_canonical_energy_loop_transport P.parent.parent P.parent.family q hr
    (P.energyLoop m) (P.energyLoop_inside_local m q hq hpos)
  obtain ⟨rP,hrP,hP⟩ := Metric.isOpen_iff.mp P.source_open q hq
  obtain ⟨rS,hrS,hS⟩ := Metric.isOpen_iff.mp isOpen_hillHminusEnergySheetSource q (real_mem_hillHminusEnergySheetSource q hr)
  let r := min rG (min rP rS)
  have hrpos : 0 < r := lt_min hrG (lt_min hrP hrS)
  have hrg : r ≤ rG := min_le_left _ _
  have hrp : r ≤ rP := (min_le_right _ _).trans (min_le_left _ _)
  have hrs : r ≤ rS := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hrpos,(ball_subset_ball hrs).trans hS,?_⟩
  intro y hy
  obtain ⟨hinside,heq⟩ := htransport y (ball_subset_ball hrg hy)
  refine ⟨hinside,?_⟩
  intro n
  rw [heq n]
  exact P.energyLoop_local_period n m y (hP (ball_subset_ball hrp hy)) hpos

end NLS.KdV.HillProductEquationPatch
