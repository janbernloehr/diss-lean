import NLS.KdV.HillPhysicalFreeDirichletDerivative
import NLS.KdV.HillNativeDirichletSheetFirstVariation
import NLS.KdV.HillAbelianFreeCorrections

/-! The actual physical root coefficient has its exact free differential.
The denominator is the nonvanishing omitted product at the actual divisor. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_physicalDirichletRootCoefficient_zero_apply (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (P.physicalDirichletRootCoefficient n) 0) h =
      -(h.val (n:ℤ)-h.val (-(n:ℤ)))/(4*P.parent.parent.miuraBall.freeFrequencyMidpoint n) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hμ := P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) 0 h0
  have ht := P.physicalDirichletFrequency_mem_disc 0 (P.real_mem_physicalDirichletSource 0 h0 hr) ((n:ℕ):ℤ)
  have hK := (P.analytic_abelianGapRootMultiplier n _ ⟨ht,h0⟩).comp
    (f := fun q => (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)) (hμ.prod analyticAt_id)
  have hS := (analyticOnNhd_hillHminusDirichletSheet n 0 (P.source_subset_canonicalDirichlet h0)).differentiableAt
  have hd := fderiv_div_apply_of_zero (hillHminusDirichletSheet n)
    (fun q => P.abelianGapRootMultiplier n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)) 0 h
    hS hK.differentiableAt (hillHminusDirichletSheet_zero n)
    (P.abelianGapRootMultiplier_ne_zero n _ ⟨ht,h0⟩)
  change (fderiv ℂ (P.physicalDirichletRootCoefficient n) 0) h = _ at hd
  rw [hd,fderiv_hillHminusDirichletSheet_zero_apply,P.abelianGapRootMultiplier_zero_divisor h0 n]
  have hτ : P.parent.parent.miuraBall.freeFrequencyMidpoint n ≠ 0 := fun hz =>
    (ne_of_gt (P.parent.parent.miuraBall.freeFrequencyMidpoint_pos
      (P.parent.subset (P.subset h0)).1 n)) (by rw [hz]; rfl)
  have hs : (Real.pi:ℂ)*(n:ℂ) ≠ 0 := mul_ne_zero
    (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)
  have hp : (-1:ℂ)^(n:ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hτ,hs,hp]
  simp only [I_sq]
  ring

end NLS.KdV.HillProductEquationPatch
