import NLS.KdV.HillHminusOnePhysicalLabels
import NLS.KdV.HillHminusOneRealGapContours
import NLS.KdV.SingularHillMovingProjection
import NLS.FunctionalAnalysis.ProjectionRank

/-! # Canonical physical gap projections and invariant rank

The canonical moving circle remains in the actual physical resolvent
for every real potential, including closed gaps. Its bounded spectral
projection varies continuously in the original H^-1 topology.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

def hillHminusPhysicalGapProjection (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) :=
  singularHillRieszProjection (periodOneSingularPotential q) (hillHminusRealGapCenter q hr n : ℂ)
    (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n)

theorem hillHminusPhysicalGapProjection_congr
    {q p : PeriodOneHminusOne} (hr : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (n : ℕ) (he : q = p) : hillHminusPhysicalGapProjection q hr n = hillHminusPhysicalGapProjection p hp n := by
  subst p
  rfl

theorem hillHminusPhysicalGapProjection_radius_pos (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    0 < hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n := by
  obtain ⟨hd,hη,_,_,_⟩ := hillHminusRealGapContour_geometry q hr n hn
  linarith

theorem hillHminusPhysicalGapProjection_resolvent (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    sphere (hillHminusRealGapCenter q hr n : ℂ)
      (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n) ⊆
        singularHillResolventSet (periodOneSingularPotential q) := by
  intro z hz
  apply (periodOneSingularHillResolvent_iff_characteristic_ne_zero q z).mpr
  exact hillHminusRadicand_ne_zero_on_realCutDomain q hr z
    (hillHminusRealGapContour_sphere_subset q hr n hn hz)

theorem continuous_hillHminusRealGapCenter_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (n : ℕ) :
    Continuous (fun t => hillHminusRealGapCenter (Q t) (hr t) n) :=
  ((continuous_hillHminusRealLabels_family Q hQ hr (2*n-1)).add
    (continuous_hillHminusRealLabels_family Q hQ hr (2*n))).div_const 2

theorem continuous_hillHminusRealGapHalfLength_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (n : ℕ) :
    Continuous (fun t => hillHminusRealGapHalfLength (Q t) (hr t) n) :=
  ((continuous_hillHminusRealLabels_family Q hQ hr (2*n)).sub
    (continuous_hillHminusRealLabels_family Q hQ hr (2*n-1))).div_const 2

theorem continuous_hillHminusRealGapCollar_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (n : ℕ) :
    Continuous (fun t => hillHminusRealGapCollar (Q t) (hr t) n) :=
  (((continuous_hillHminusRealLabels_family Q hQ hr (2*n-1)).sub
    (continuous_hillHminusRealLabels_family Q hQ hr (2*n-2))).min
    ((continuous_hillHminusRealLabels_family Q hQ hr (2*n+1)).sub
      (continuous_hillHminusRealLabels_family Q hQ hr (2*n)))).div_const 4

theorem continuous_hillHminusPhysicalGapProjection_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun t => hillHminusPhysicalGapProjection (Q t) (hr t) n) := by
  exact continuous_singularHillRieszProjection_moving
    (fun t => periodOneSingularPotential (Q t)) (periodOneSingularPotential.continuous.comp hQ)
    (fun t => (hillHminusRealGapCenter (Q t) (hr t) n : ℂ))
    (Complex.continuous_ofReal.comp (continuous_hillHminusRealGapCenter_family Q hQ hr n))
    (fun t => hillHminusRealGapHalfLength (Q t) (hr t) n+hillHminusRealGapCollar (Q t) (hr t) n)
    ((continuous_hillHminusRealGapHalfLength_family Q hQ hr n).add
      (continuous_hillHminusRealGapCollar_family Q hQ hr n))
    (fun t => (hillHminusPhysicalGapProjection_radius_pos (Q t) (hr t) n hn).le)
    (fun t => hillHminusPhysicalGapProjection_resolvent (Q t) (hr t) n hn)

theorem hillHminusPhysicalGapProjection_rank_eq_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℂ (hillHminusPhysicalGapProjection q hr n).range =
      Module.finrank ℂ (hillHminusPhysicalGapProjection 0 (by intro k; simp) n).range := by
  let Q : ℝ → PeriodOneHminusOne := fun t => (t : ℂ) • q
  have hQ : Continuous Q := by dsimp only [Q]; fun_prop
  have hreal (t : ℝ) : IsRealPeriodOneHminusOne (Q t) := hr.smul_real t
  let P := fun t => hillHminusPhysicalGapProjection (Q t) (hreal t) n
  have hcont : Continuous P := continuous_hillHminusPhysicalGapProjection_family Q hQ hreal n hn
  have hid (t : ℝ) : IsIdempotentElem (P t) := isIdempotentElem_singularHillRieszProjection _ _ _
    (hillHminusPhysicalGapProjection_radius_pos _ _ n hn) (hillHminusPhysicalGapProjection_resolvent _ _ n hn)
  have hfin (t : ℝ) : FiniteDimensional ℂ (P t).range := finiteDimensional_singularHillRieszProjection_range _ _ _
    (hillHminusPhysicalGapProjection_radius_pos _ _ n hn) (hillHminusPhysicalGapProjection_resolvent _ _ n hn)
  have he := NLS.ProjectionRank.finrank_eq_on_preconnected isPreconnected_Icc P hcont.continuousOn
    (fun t _ => hid t) (fun t _ => hfin t) (a := 1) (b := 0)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1) (by constructor <;> norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hQ1 : Q 1 = q := by simp only [Q,Complex.ofReal_one,one_smul]
  have hQ0 : Q 0 = 0 := by simp only [Q,Complex.ofReal_zero,zero_smul]
  have hP1 := hillHminusPhysicalGapProjection_congr (hreal 1) hr n hQ1
  have hP0 := hillHminusPhysicalGapProjection_congr (hreal 0) (by intro k; simp) n hQ0
  change Module.finrank ℂ (P 1).range = Module.finrank ℂ (P 0).range at he
  change P 1 = hillHminusPhysicalGapProjection q hr n at hP1
  change P 0 = hillHminusPhysicalGapProjection 0 _ n at hP0
  rw [hP1,hP0] at he
  exact he

end NLS.KdV
