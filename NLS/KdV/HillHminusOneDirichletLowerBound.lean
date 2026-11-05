import NLS.KdV.HillHminusRealPhysicalChart
import NLS.KdV.HillHminusOneRealMiuraCharts
import NLS.KdV.HillHminusOnePhysicalDirichlet
import NLS.MKdV.L2QuasiHillDirichletPositive

/-! # Locally uniform strict lower bounds for actual H^-1 Dirichlet roots

A real-preserving analytic Miura chart has one fixed real energy shift.
Its physical factorization gives a strict lower bound for every real
Dirichlet root at every real input in that same complex-open chart.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open MeasureTheory hiding extend
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem HillHminusMiuraChart.dirichlet_root_gt_neg_shift_square
    (C : HillHminusMiuraChart) (c : ℝ) (hc : C.energyShift = (c : ℂ)^2)
    (p : PeriodOneHminusOne) (hp : p ∈ C.domain) (hu : star (C.physicalProfile p) = C.physicalProfile p)
    (x : ℝ) (hz : hillHminusDirichlet p x = 0) : -(c^2) < x := by
  have he : (x : ℂ)+C.energyShift = ((x+c^2 : ℝ) : ℂ) := by rw [hc]; push_cast; rfl
  have hzero := (C.hillHminusDirichlet_eq_physicalPosition p hp x).symm.trans hz
  change extend (l2QuasiHillPosition (C.physicalProfile p) ((x : ℂ)+C.energyShift) (0,1)) 1 = 0 at hzero
  rw [he] at hzero
  have h := l2QuasiHillDirichlet_energy_pos_of_real_profile (C.physicalProfile p) hu (x+c^2) hzero
  linarith

theorem exists_hillHminusDirichlet_local_uniform_lower_bound
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ ∃ L : ℝ,
      ∀ p ∈ U, IsRealPeriodOneHminusOne p → ∀ x : ℝ, hillHminusDirichlet p x = 0 → L < x := by
  obtain ⟨C,hq,c,_,hc,hreal⟩ := exists_hillHminus_real_Miura_chart q hr
  exact ⟨C.domain,C.domain_open,hq,-(c^2),fun p hp hpr x hz =>
    C.dirichlet_root_gt_neg_shift_square c hc p hp (hreal p hp hpr) x hz⟩

end NLS.KdV
