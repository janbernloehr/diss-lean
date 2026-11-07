import NLS.KdV.HillPhysicalDirichletSheetCoefficient

/-! Actual physical Dirichlet-divisor values of the off-index Hill
Abelian family. The terminal is the AUXILIARY frequency and the sheet
is the ACTUAL norming multiplier sheet. Both may reach branch points;
the formula stays analytic without dividing by their values. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def physicalOffIndexAbelianValue (P : HillProductEquationPatch) (n m : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  P.physicalDirichletRootCoefficient m q*
    P.offIndexAbelianFilledQuotient n m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)

theorem analytic_physicalOffIndexAbelianValue (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (P.physicalOffIndexAbelianValue n m) P.physicalDirichletSource := by
  intro q hq
  exact P.analyticAt_offIndexAbelian_filled_terminal_value n m hmn _ _ q hq.1
    (P.analytic_physicalDirichletFrequency ((m:ℕ):ℤ) q hq.1)
    (P.analytic_physicalDirichletRootCoefficient m q hq) (P.physicalDirichletFrequency_mem_disc q hq _)

theorem physicalDirichletRootCoefficient_preserves_sheet (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)*P.physicalDirichletRootCoefficient m q =
      hillHminusDirichletSheet m q := by
  unfold physicalDirichletRootCoefficient
  exact mul_div_cancel₀ _ (P.abelianGapRootMultiplier_ne_zero m _ ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩)

theorem physicalOffIndexAbelianValue_zero_of_sheet_zero (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hs : hillHminusDirichletSheet m q = 0) : P.physicalOffIndexAbelianValue n m q = 0 := by
  simp only [physicalOffIndexAbelianValue,physicalDirichletRootCoefficient,hs,zero_div,zero_mul]

theorem physicalDirichletRootCoefficient_zero_iff_endpoint (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    P.physicalDirichletRootCoefficient m q = 0 ↔
      P.physicalDirichletFrequency ((m:ℕ):ℤ) q = canonicalPeriodicLeft (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ) ∨
      P.physicalDirichletFrequency ((m:ℕ):ℤ) q = canonicalPeriodicRight (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ) := by
  have hs := P.physicalDirichletRootCoefficient_sq m q hq
  rw [sourceAngularSelectedPolynomial_eq_endpoint_factor] at hs
  constructor
  · intro h
    rw [h,zero_pow (by decide : (2:ℕ) ≠ 0)] at hs
    rcases mul_eq_zero.mp hs.symm with hl | hr
    · exact Or.inl (sub_eq_zero.mp hl).symm
    · exact Or.inr (sub_eq_zero.mp hr).symm
  · intro h
    apply eq_zero_of_pow_eq_zero
    rw [hs]
    rcases h with h | h <;> rw [h] <;> simp

theorem norm_physicalOffIndexAbelianValue_le (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ‖P.physicalOffIndexAbelianValue n m q‖ ≤
      (‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖/2)*
        ‖P.offIndexAbelianFilledQuotient n m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)‖ := by
  rw [physicalOffIndexAbelianValue,norm_mul]
  exact mul_le_mul_of_nonneg_right (P.norm_physicalDirichletRootCoefficient_le m q hq) (norm_nonneg _)

theorem physicalOffIndexAbelianValue_eq_improper_integral_on_cut_complement (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hcut : P.physicalDirichletFrequency ((m:ℕ):ℤ) q ∈ P.abelianGapDisc m q)
    (hne : P.physicalDirichletRootCoefficient m q ≠ 0) :
    P.physicalOffIndexAbelianValue n m q =
      (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) (P.physicalDirichletFrequency ((m:ℕ):ℤ) q)/
        P.physicalDirichletRootCoefficient m q)*P.offIndexAbelianEndpointIntegral n m q (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) := by
  let μ := P.physicalDirichletFrequency ((m:ℕ):ℤ) q
  have hs : (P.physicalDirichletRootCoefficient m q)^2 =
      (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) μ)^2 :=
    (P.physicalDirichletRootCoefficient_sq m q hq).trans
      ((sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) μ hcut.2).trans
        (sourceAngularSelectedPolynomial_eq_endpoint_factor (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) μ).symm).symm
  have he := P.offIndexAbelianRegularSheetPrimitive_root_ratio n m
    (fun t : ℂ × PeriodOneHminusOne => P.physicalDirichletRootCoefficient m t.2) (μ,q) hne hs
  rw [← P.offIndexAbelianEndpointIntegral_eq_filled_root_product n m hmn q hq.1 μ hcut] at he
  exact he

end NLS.KdV.HillProductEquationPatch
