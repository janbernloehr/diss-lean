import NLS.SequenceSpaces.PeriodOneConstantCoefficients
import NLS.KdV.HillHminusFreeLabels
import NLS.KdV.HminusOneMiuraTrace

/-! Constant-potential translation of the ENTIRE original native Hill
labeling. Analytic multiplicities and ordered-enumeration uniqueness
retain every low, repeated and high occurrence. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusRadicand_add_constant (q : PeriodOneHminusOne) (c μ : ℂ) :
    hillHminusRadicand (q+periodOneConstantCLM c) (μ+c) = hillHminusRadicand q μ := by
  rw [hillHminusRadicand,hillHminusRadicand,periodOneConstantCLM_eq_L2_single,
    hillHminusDiscriminant_add_const]

theorem analyticOrderNatAt_hillHminusRadicand_add_constant (q : PeriodOneHminusOne) (c μ : ℂ) :
    analyticOrderNatAt (hillHminusRadicand (q+periodOneConstantCLM c)) (μ+c) =
      analyticOrderNatAt (hillHminusRadicand q) μ := by
  have hg : AnalyticAt ℂ (fun z : ℂ => z+c) μ := analyticAt_id.add analyticAt_const
  have hd : deriv (fun z : ℂ => z+c) μ ≠ 0 := by
    have hh : HasDerivAt (fun z : ℂ => z+c) 1 μ := by
      simpa only [id_eq] using (hasDerivAt_id μ).add_const c
    rw [hh.deriv]
    exact one_ne_zero
  have ho := analyticOrderAt_comp_of_deriv_ne_zero
    (f := hillHminusRadicand (q+periodOneConstantCLM c)) hg hd
  have he : hillHminusRadicand (q+periodOneConstantCLM c) ∘ (fun z : ℂ => z+c) =
      hillHminusRadicand q := funext (fun z => hillHminusRadicand_add_constant q c z)
  rw [he] at ho
  exact congrArg ENat.toNat ho.symm

theorem hillHminusLabels_add_constant (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (c : ℝ) (hs : IsRealPeriodOneHminusOne (q+periodOneConstantCLM (c:ℂ))) :
    hillHminusLabels (q+periodOneConstantCLM (c:ℂ)) hs = fun j => hillHminusLabels q hr j+c := by
  have hf (x : ℝ) : {j | hillHminusLabels q hr j+c=x}.Finite := by
    have he : {j | hillHminusLabels q hr j+c=x} = {j | hillHminusLabels q hr j=x-c} := by
      ext j
      change (hillHminusLabels q hr j+c=x) ↔ hillHminusLabels q hr j=x-c
      constructor <;> intro hj <;> linarith
    rw [he]
    exact hillHminusLabels_finite_fiber q hr (x-c)
  apply ordered_nat_enumeration_eq_of_multiplicity _ _
    (hillHminusLabels_finite_fiber _ hs) hf (monotone_hillHminusLabels _ hs)
    (fun _ _ hij => by linarith [monotone_hillHminusLabels q hr hij])
  intro x
  have he (j : ℕ) : (hillHminusLabels q hr j+c=x) ↔ hillHminusLabels q hr j=x-c :=
    by constructor <;> intro hj <;> linarith
  simp only [he]
  rw [hillHminusLabels_global_multiplicity,hillHminusLabels_global_multiplicity]
  have ho := analyticOrderNatAt_hillHminusRadicand_add_constant q (c:ℂ) ((x-c:ℝ):ℂ)
  simpa only [Complex.ofReal_sub,sub_add_cancel] using ho

end NLS.KdV
