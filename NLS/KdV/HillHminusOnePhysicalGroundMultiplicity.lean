import NLS.KdV.HillHminusOnePhysicalGapProjection
import NLS.KdV.SingularHillProjectionRootPair
import NLS.KdV.SingularHillFreeGround

/-! # The actual original ground eigenvalue has algebraic multiplicity one

A continuously moving physical circle isolates the lowest label along
all real potential paths. Its projection retains the one-dimensional
original free ground range in the full H^-1 topology.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

def hillHminusPhysicalGroundRadius (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : ℝ :=
  (hillHminusRealLabels q hr 1-hillHminusRealLabels q hr 0)/2

def hillHminusPhysicalGroundProjection (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :=
  singularHillRieszProjection (periodOneSingularPotential q) (hillHminusRealLabels q hr 0 : ℂ)
    (hillHminusPhysicalGroundRadius q hr)

theorem hillHminusPhysicalGroundRadius_pos (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    0 < hillHminusPhysicalGroundRadius q hr := by
  have h := hillHminusRealLabels_band_strict q hr 0
  change hillHminusRealLabels q hr 0 < hillHminusRealLabels q hr 1 at h
  dsimp only [hillHminusPhysicalGroundRadius]
  linarith

theorem hillHminusPhysicalGroundProjection_only_center
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ)
    (hz : z ∈ closedBall (hillHminusRealLabels q hr 0 : ℂ) (hillHminusPhysicalGroundRadius q hr))
    (hzero : hillHminusRadicand q z = 0) : z = (hillHminusRealLabels q hr 0 : ℂ) := by
  obtain ⟨j,rfl⟩ := (hillHminusRealLabels_root_iff q hr z).mp hzero
  by_cases hj : j = 0
  · subst j
    rfl
  have hm := monotone_hillHminusRealLabels q hr (show 1 ≤ j by omega)
  have hnon := monotone_hillHminusRealLabels q hr (Nat.zero_le j)
  have hstrict := hillHminusRealLabels_band_strict q hr 0
  have hd := mem_closedBall.mp hz
  rw [dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hnon)] at hd
  dsimp only [hillHminusPhysicalGroundRadius] at hd
  change hillHminusRealLabels q hr 0 < hillHminusRealLabels q hr 1 at hstrict
  exfalso
  linarith

theorem hillHminusPhysicalGroundProjection_resolvent (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    sphere (hillHminusRealLabels q hr 0 : ℂ) (hillHminusPhysicalGroundRadius q hr) ⊆
      singularHillResolventSet (periodOneSingularPotential q) := by
  intro z hz
  apply (periodOneSingularHillResolvent_iff_characteristic_ne_zero q z).mpr
  intro hzero
  have he := hillHminusPhysicalGroundProjection_only_center q hr z (sphere_subset_closedBall hz) hzero
  have hd := mem_sphere.mp hz
  rw [he,dist_self] at hd
  have hp := hillHminusPhysicalGroundRadius_pos q hr
  linarith

theorem hillHminusPhysicalGroundProjection_rank_eq_multiplicity
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    Module.finrank ℂ (hillHminusPhysicalGroundProjection q hr).range =
      singularHillAlgebraicMultiplicity (periodOneSingularPotential q) (hillHminusRealLabels q hr 0) := by
  exact singularHillRieszProjection_rank_eq_single_multiplicity _ (periodOneSingularPotential_real q hr) _ _
    (hillHminusPhysicalGroundRadius_pos q hr) (hillHminusPhysicalGroundProjection_resolvent q hr) _
    (mem_ball_self (hillHminusPhysicalGroundRadius_pos q hr))
    (fun z hz hspec => hillHminusPhysicalGroundProjection_only_center q hr z (ball_subset_closedBall hz)
      ((periodOneSingularHillSpectrum_iff_characteristic q z).mp hspec))

theorem continuous_hillHminusPhysicalGroundProjection_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) :
    Continuous (fun t => hillHminusPhysicalGroundProjection (Q t) (hr t)) := by
  exact continuous_singularHillRieszProjection_moving
    (fun t => periodOneSingularPotential (Q t)) (periodOneSingularPotential.continuous.comp hQ)
    (fun t => (hillHminusRealLabels (Q t) (hr t) 0 : ℂ))
    (Complex.continuous_ofReal.comp (continuous_hillHminusRealLabels_family Q hQ hr 0))
    (fun t => hillHminusPhysicalGroundRadius (Q t) (hr t))
    (((continuous_hillHminusRealLabels_family Q hQ hr 1).sub
      (continuous_hillHminusRealLabels_family Q hQ hr 0)).div_const 2)
    (fun t => (hillHminusPhysicalGroundRadius_pos (Q t) (hr t)).le)
    (fun t => hillHminusPhysicalGroundProjection_resolvent (Q t) (hr t))

theorem hillHminusPhysicalGroundProjection_congr
    {q p : PeriodOneHminusOne} (hr : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (he : q = p) : hillHminusPhysicalGroundProjection q hr = hillHminusPhysicalGroundProjection p hp := by
  subst p
  rfl

theorem hillHminusPhysicalGroundProjection_rank_eq_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    Module.finrank ℂ (hillHminusPhysicalGroundProjection q hr).range =
      Module.finrank ℂ (hillHminusPhysicalGroundProjection 0 (by intro k; simp)).range := by
  let Q : ℝ → PeriodOneHminusOne := fun t => (t : ℂ) • q
  have hQ : Continuous Q := by dsimp only [Q]; fun_prop
  have hreal (t : ℝ) : IsRealPeriodOneHminusOne (Q t) := hr.smul_real t
  let P := fun t => hillHminusPhysicalGroundProjection (Q t) (hreal t)
  have hcont : Continuous P := continuous_hillHminusPhysicalGroundProjection_family Q hQ hreal
  have hid (t : ℝ) : IsIdempotentElem (P t) := isIdempotentElem_singularHillRieszProjection _ _ _
    (hillHminusPhysicalGroundRadius_pos _ _) (hillHminusPhysicalGroundProjection_resolvent _ _)
  have hfin (t : ℝ) : FiniteDimensional ℂ (P t).range := finiteDimensional_singularHillRieszProjection_range _ _ _
    (hillHminusPhysicalGroundRadius_pos _ _) (hillHminusPhysicalGroundProjection_resolvent _ _)
  have he := NLS.ProjectionRank.finrank_eq_on_preconnected isPreconnected_Icc P hcont.continuousOn
    (fun t _ => hid t) (fun t _ => hfin t) (a := 1) (b := 0)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1) (by constructor <;> norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hQ1 : Q 1 = q := by simp only [Q,Complex.ofReal_one,one_smul]
  have hQ0 : Q 0 = 0 := by simp only [Q,Complex.ofReal_zero,zero_smul]
  have hP1 := hillHminusPhysicalGroundProjection_congr (hreal 1) hr hQ1
  have hP0 := hillHminusPhysicalGroundProjection_congr (hreal 0) (by intro k; simp) hQ0
  change Module.finrank ℂ (P 1).range = Module.finrank ℂ (P 0).range at he
  change P 1 = hillHminusPhysicalGroundProjection q hr at hP1
  change P 0 = hillHminusPhysicalGroundProjection 0 _ at hP0
  rw [hP1,hP0] at he
  exact he

theorem hillHminusPhysicalGroundProjection_rank_zero (hr : IsRealPeriodOneHminusOne 0) :
    Module.finrank ℂ (hillHminusPhysicalGroundProjection 0 hr).range = 1 := by
  rw [hillHminusPhysicalGroundProjection_rank_eq_multiplicity,map_zero,hillHminusRealLabels_zero]
  norm_num [freeHillValue,singularHillAlgebraicMultiplicity_zero_ground]

theorem hillHminusPhysicalGroundProjection_rank_one (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    Module.finrank ℂ (hillHminusPhysicalGroundProjection q hr).range = 1 :=
  (hillHminusPhysicalGroundProjection_rank_eq_zero q hr).trans (hillHminusPhysicalGroundProjection_rank_zero _)

theorem hillHminusLowestRealRoot_physical_multiplicity_one
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    singularHillAlgebraicMultiplicity (periodOneSingularPotential q) (hillHminusLowestRealRoot q hr) = 1 := by
  rw [← hillHminusRealLabels_zero_eq_lowest q hr]
  exact (hillHminusPhysicalGroundProjection_rank_eq_multiplicity q hr).symm.trans
    (hillHminusPhysicalGroundProjection_rank_one q hr)

end NLS.KdV
