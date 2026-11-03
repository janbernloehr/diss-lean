import NLS.KdV.HillHminusOneWeakEquation
import NLS.KdV.HillHminusOneTraceParity
import NLS.MKdV.L2QuasiHillMultipliers

/-! # Canonical H^-1 roots give actual nonzero scalar weak eigenfunctions

The intrinsic discriminant characterizes every complex Floquet state of
the actual rough initial-value problem. Every real canonical label has
a nonzero H1 position, the exact indexed periodic/antiperiodic state
multiplier, and the corresponding scalar weak equation. The converse
from arbitrary weak solutions and a chart-independent operator domain
are separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV.HillHminusMiuraChart

theorem hillHminusDiscriminant_eq_physicalQuasi (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDiscriminant q lambda = l2QuasiHillDiscriminant (C.physicalProfile q) (lambda+C.energyShift) :=
  C.hillHminusDiscriminant_eq_physicalSolution_trace q hq lambda

theorem hillHminusDiscriminant_multiplier_iff (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (lambda σ : ℂ) :
    σ^2-hillHminusDiscriminant q lambda*σ+1 = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  rw [C.hillHminusDiscriminant_eq_physicalQuasi q hq lambda]
  exact l2QuasiHillDiscriminant_multiplier_iff _ _ _

theorem hillHminusDiscriminant_eq_two_iff (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDiscriminant q lambda = 2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = v := by
  rw [C.hillHminusDiscriminant_eq_physicalQuasi q hq lambda]
  exact l2QuasiHillDiscriminant_eq_two_iff _ _

theorem hillHminusDiscriminant_eq_neg_two_iff (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDiscriminant q lambda = -2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = -v := by
  rw [C.hillHminusDiscriminant_eq_physicalQuasi q hq lambda]
  exact l2QuasiHillDiscriminant_eq_neg_two_iff _ _

theorem hillHminusRadicand_eq_zero_iff_physicalSolution (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusRadicand q lambda = 0 ↔
      (∃ v : ℂ × ℂ, v ≠ 0 ∧ C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = v) ∨
      (∃ v : ℂ × ℂ, v ≠ 0 ∧ C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = -v) := by
  rw [hillHminusRadicand,show hillHminusDiscriminant q lambda^2-4 =
    (hillHminusDiscriminant q lambda-2)*(hillHminusDiscriminant q lambda+2) by ring,
    mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg,
    C.hillHminusDiscriminant_eq_two_iff q hq lambda,C.hillHminusDiscriminant_eq_neg_two_iff q hq lambda]

/-- Every label, including central and collapsed-gap labels, gives a
nonzero H1 weak scalar eigenfunction with the exact indexed endpoint sign. -/
theorem exists_nonzero_weak_solution_at_label (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (hr : IsRealPeriodOneHminusOne q) (j : ℕ) :
    ∃ v : ℂ × ℂ, v ≠ 0 ∧ C.physicalPosition q (hillHminusRealLabels q hr j) v ≠ 0 ∧
      AbsolutelyContinuousOnInterval (extend (C.physicalPosition q (hillHminusRealLabels q hr j) v)) 0 1 ∧
      MemLp (deriv (extend (C.physicalPosition q (hillHminusRealLabels q hr j) v)))
        2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      C.physicalSolution q (hillHminusRealLabels q hr j) v ⟨1,by constructor <;> norm_num⟩ =
        (-1 : ℂ)^((j+1)/2) • v ∧
      ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
        MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
        extend φ 1 = (-1 : ℂ)^((j+1)/2)*extend φ 0 →
        shiftedMiuraWeakForm (C.physicalProfile q) C.energyShift (C.physicalPosition q (hillHminusRealLabels q hr j) v) φ =
          (hillHminusRealLabels q hr j : ℂ)*(∫ s in (0 : ℝ)..1,
            extend (C.physicalPosition q (hillHminusRealLabels q hr j) v) s*extend φ s) := by
  let σ : ℂ := (-1)^((j+1)/2)
  have hσ : σ^2 = 1 := by
    dsimp only [σ]
    rw [← pow_mul,mul_comm ((j+1)/2) 2,pow_mul]
    norm_num
  have hp : σ^2-hillHminusDiscriminant q (hillHminusRealLabels q hr j)*σ+1 = 0 := by
    rw [hillHminusRealLabels_trace_parity q hr j]
    change σ^2-2*σ*σ+1 = 0
    linear_combination -hσ
  obtain ⟨v,hv,he⟩ := (C.hillHminusDiscriminant_multiplier_iff q hq (hillHminusRealLabels q hr j) σ).mp hp
  have hH := C.physicalSolution_scalar_H1 q (hillHminusRealLabels q hr j) v
  refine ⟨v,hv,C.physicalPosition_ne_zero q _ v hv,hH.1,hH.2.1,he,?_⟩
  intro φ hφ hφ₂ hφend
  exact C.physicalSolution_weak_equation_floquet q _ σ σ (by simpa only [pow_two] using hσ)
    v he φ hφ hφ₂ hφend

end NLS.KdV.HillHminusMiuraChart
