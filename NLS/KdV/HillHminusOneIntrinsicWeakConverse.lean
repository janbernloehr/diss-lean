import NLS.KdV.HillHminusOneIntrinsicWeakSolutions
import NLS.MKdV.L2QuasiHillWeakFloquetConverse

/-! # Exact intrinsic weak Floquet spectrum of the H^-1 Hill discriminant

Every arbitrary intrinsic scalar weak eigenfunction is recovered as an
actual nonzero initial-value state in every Miura chart. Both state
endpoint conditions follow from the scalar formulation. Consequently
the intrinsic weak Floquet problem is equivalent to the discriminant's
characteristic equation, and its real periodic/antiperiodic energies are
exactly the canonical labels. Closed/self-adjoint operator domains and
spectral multiplicity identification remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

/-- Recovery holds in every chart, without assuming a momentum or its
endpoint condition as part of the scalar weak eigenfunction data. -/
theorem HillHminusMiuraChart.exists_physicalState_of_intrinsic_weak_eigenfunction
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (lambda σ : ℂ) (y : Curve ℂ) (hy : IsIntrinsicHillWeakEigenfunction q lambda σ y) :
    ∃ v : ℂ × ℂ, v ≠ 0 ∧ y = C.physicalPosition q lambda v ∧
      C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  obtain ⟨hσ,hy0,hyAC,hy₂,hyend,hw⟩ := hy
  apply exists_nonzero_Floquet_initial_state_of_weak_equation (C.physicalProfile q) C.energyShift
    lambda σ hσ y hy0 hyAC hy₂ hyend
  intro φ hφ hφ₂ hφend
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by
    rw [hyend,hφend]
    calc
      _ = (σ*σ⁻¹)*(extend y 0*extend φ 0) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hσ,one_mul]
  rw [← hillHminusWeakForm_eq_chart C q hq y φ hyAC hφ hy₂ hφ₂ hend]
  exact hw φ hφ hφ₂ hφend

theorem characteristic_eq_zero_of_intrinsic_weak_eigenfunction (q : PeriodOneHminusOne)
    (lambda σ : ℂ) (y : Curve ℂ) (hy : IsIntrinsicHillWeakEigenfunction q lambda σ y) :
    σ^2-hillHminusDiscriminant q lambda*σ+1 = 0 := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  obtain ⟨v,hv,_,he⟩ := C.exists_physicalState_of_intrinsic_weak_eigenfunction q hq lambda σ y hy
  exact (C.hillHminusDiscriminant_multiplier_iff q hq lambda σ).mpr ⟨v,hv,he⟩

/-- All potentials, all energies and all complex multiplier parameters
are included; zero multiplier is excluded by both sides themselves. -/
theorem exists_intrinsic_weak_eigenfunction_iff_characteristic (q : PeriodOneHminusOne) (lambda σ : ℂ) :
    (∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda σ y) ↔
      σ^2-hillHminusDiscriminant q lambda*σ+1 = 0 := by
  constructor
  · rintro ⟨y,hy⟩
    exact characteristic_eq_zero_of_intrinsic_weak_eigenfunction q lambda σ y hy
  · exact exists_intrinsic_weak_eigenfunction_of_multiplier q lambda σ

theorem not_intrinsic_weak_eigenfunction_zero_multiplier (q : PeriodOneHminusOne) (lambda : ℂ) (y : Curve ℂ) :
    ¬ IsIntrinsicHillWeakEigenfunction q lambda 0 y := fun h => h.1 rfl

theorem hillHminusDiscriminant_eq_two_iff_intrinsic_weak (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDiscriminant q lambda = 2 ↔
      ∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda 1 y := by
  rw [exists_intrinsic_weak_eigenfunction_iff_characteristic]
  constructor <;> intro h <;> linear_combination -h

theorem hillHminusDiscriminant_eq_neg_two_iff_intrinsic_weak (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDiscriminant q lambda = -2 ↔
      ∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda (-1) y := by
  rw [exists_intrinsic_weak_eigenfunction_iff_characteristic]
  constructor <;> intro h <;> linear_combination h

theorem hillHminusRadicand_eq_zero_iff_intrinsic_weak (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusRadicand q lambda = 0 ↔
      (∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda 1 y) ∨
      (∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda (-1) y) := by
  rw [hillHminusRadicand,show hillHminusDiscriminant q lambda^2-4 =
    (hillHminusDiscriminant q lambda-2)*(hillHminusDiscriminant q lambda+2) by ring,
    mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg,
    hillHminusDiscriminant_eq_two_iff_intrinsic_weak,hillHminusDiscriminant_eq_neg_two_iff_intrinsic_weak]

/-- The canonical list exhausts the actual intrinsic weak periodic and
antiperiodic energies, including the lowest and collapsed-gap labels. -/
theorem intrinsic_weak_periodic_or_antiperiodic_iff_real_label (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    ((∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda 1 y) ∨
      (∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda (-1) y)) ↔
      ∃ j : ℕ, lambda = (hillHminusRealLabels q hr j : ℂ) :=
  (hillHminusRadicand_eq_zero_iff_intrinsic_weak q lambda).symm.trans (hillHminusRealLabels_root_iff q hr lambda)

theorem intrinsic_weak_periodic_or_antiperiodic_energy_im_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ)
    (h : (∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda 1 y) ∨
      (∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda (-1) y)) : lambda.im = 0 := by
  obtain ⟨j,hj⟩ := (intrinsic_weak_periodic_or_antiperiodic_iff_real_label q hr lambda).mp h
  rw [hj,ofReal_im]

end NLS.KdV
