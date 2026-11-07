import NLS.KdV.MiuraHillEnergyRootIndependence
import NLS.KdV.HillHminusOneMiuraHigherAction
import NLS.KdV.HillMiuraPositiveGaps
import NLS.ZakharovShabat.SourcePositivePeriodCircle

/-! Actual normalized Hill energy-cycle periods. The cycles are literal
quadratic images of positive original circles, have winding one, and lie
in the jointly analytic nonzero energy-root domain. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace MiuraHillPsiFamily

/-- The entire actual image loop lies in the energy sheet's cut complement. -/
theorem energyCircle_inside (A : MiuraHillPsiFamily) (u : Coeff 2) (hu : u ∈ A.source)
    (c : ℂ) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) c).Inside
      {E : ℂ | (E,u) ∈ A.energyRootDomain c} := by
  intro i t
  let z := (PiecewiseC1Loop.circle (D.center:ℂ) D.radius).edge i t
  have hz : z ∈ sphere (D.center:ℂ) D.radius :=
    circleMap_mem_sphere (D.center:ℂ) D.radius_pos.le ((2*Real.pi)*(t:ℝ))
  have hb := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
  have hzr : 0 < z.re := by linarith [hb.1]
  exact A.squared_energy_mem_rootDomain u hu c z hzr (D.sphere_subset_rootDomain hz)

/-- Exact period of the actual differential on the actual oriented energy loop. -/
theorem differential_energyCircle_period (A : MiuraHillPsiFamily) (n m : ℕ+)
    (u : Coeff 2) (hu : u ∈ A.source) (c : ℂ)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop
      (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) c).integral
      (fun E => A.differential n c (E,u)) = if m = n then 1 else 0 := by
  let Γ := PiecewiseC1Loop.circle (D.center:ℂ) D.radius
  have hΓ : Γ.Inside {z : ℂ | 0 < z.re} := by
    intro i t
    have hz : Γ.edge i t ∈ sphere (D.center:ℂ) D.radius :=
      circleMap_mem_sphere (D.center:ℂ) D.radius_pos.le ((2*Real.pi)*(t:ℝ))
    have hb := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
    change 0 < (Γ.edge i t).re
    linarith [hb.1]
  have he : (quadraticEnergyLoop Γ c).integral (fun E => A.differential n c (E,u)) =
      Γ.integral (fun z => (2*z*A.numerator n (z^2,u))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u) z) := by
    apply integral_quadraticEnergyLoop Γ c _ _ _ hΓ
    intro z hz
    rw [differential,sub_add_cancel,hillHminusMiuraRoot_at_squared_energy u c z hz]
    ring
  rw [he,PiecewiseC1Loop.integral_circle]
  exact A.numerator_pullback_period n m u hu D

/-- Positive cycles exist at EVERY positive index of EVERY real L2 Miura source. -/
theorem exists_positive_energyCircle (A : MiuraHillPsiFamily) (u : PeriodOneRealL2) (c : ℂ) (m : ℕ+) :
    ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ),
      0 < D.center-D.radius ∧
      (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) c).Inside
        {E : ℂ | (E,u.val) ∈ A.energyRootDomain c} ∧
      (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) c).windingIntegral
        ((sourceStandardRootMidpoint (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))^2-c) = 1 ∧
      ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop
        (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) c).integral
        (fun E => A.differential n c (E,u.val)) = if m = n then 1 else 0 := by
  obtain ⟨D,hD⟩ := exists_positive_sourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u) ((m:ℕ):ℤ)
    (hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos))
  exact ⟨D,hD,A.energyCircle_inside u.val (A.real_mem_source u) c m D hD,
    winding_one_miura_action_contour u.val c ((m:ℕ):ℤ) D hD,
    fun n => A.differential_energyCircle_period n m u.val (A.real_mem_source u) c D hD⟩

end MiuraHillPsiFamily
end NLS.KdV
