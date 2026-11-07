import NLS.KdV.HillFreeRootMultiplier
import NLS.KdV.HillAbelianPhysicalEnergyPullback
import NLS.KdV.HillPhysicalDirichletSheetCoefficient

/-! The ACTUAL auxiliary Dirichlet frequency is the positive free
collapsed midpoint. The physical omitted multiplier has its exact signed
value at this actual divisor, including every positive original index. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem physicalDirichletFrequency_zero_eq_midpoint (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) :
    P.physicalDirichletFrequency ((n:ℕ):ℤ) 0 = P.parent.parent.miuraBall.freeFrequencyMidpoint n := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hB := (P.parent.subset (P.subset h0)).1
  have hμpos := P.abelianGapDisc_re_pos_of_real n 0 h0 hr _
    (P.physicalDirichletFrequency_mem_disc 0 (P.real_mem_physicalDirichletSource 0 h0 hr) ((n:ℕ):ℤ))
  have hτpos := P.parent.parent.miuraBall.freeFrequencyMidpoint_pos hB n
  have hμ := P.physicalDirichletFrequency_energy n 0 h0
  rw [hillHminusCanonicalDirichlet_zero_eq_sq] at hμ
  have hτ := P.parent.parent.miuraBall.freeFrequencyMidpoint_energy hB n
  exact quadraticEnergyMap_injOn_right _ hμpos hτpos (hμ.trans hτ.symm)

theorem abelianGapRootMultiplier_zero_midpoint (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) :
    P.abelianGapRootMultiplier n (P.parent.parent.miuraBall.freeFrequencyMidpoint n,0) =
      2*I*(-1:ℂ)^(n:ℕ)*P.parent.parent.miuraBall.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) := by
  exact P.parent.parent.miuraBall.freeRootMultiplier_value (P.parent.subset (P.subset h0)).1 n

theorem abelianGapRootMultiplier_zero_divisor (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) :
    P.abelianGapRootMultiplier n (P.physicalDirichletFrequency ((n:ℕ):ℤ) 0,0) =
      2*I*(-1:ℂ)^(n:ℕ)*P.parent.parent.miuraBall.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) := by
  rw [P.physicalDirichletFrequency_zero_eq_midpoint h0 n]
  exact P.abelianGapRootMultiplier_zero_midpoint h0 n

end NLS.KdV.HillProductEquationPatch
