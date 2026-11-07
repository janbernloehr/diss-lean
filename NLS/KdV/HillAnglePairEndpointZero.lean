import NLS.KdV.HillSignedSheetCotangents
import NLS.KdV.HillAnglePairActionStationarity

/-! At every real source whose actual Dirichlet terminals are all
periodic, the ACTUAL complete Abelian angle/angle bracket has zero
value. The full infinite corrections are retained by the proved
operator-norm cotangent limits. Transport to other sources is separate. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

theorem fderiv_completePhase_eq_add (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hc : q ∈ hillHminusOffIndexAnalyticDomain) :
    fderiv ℂ C.completePhase q=fderiv ℂ C.phase q+fderiv ℂ (hillHminusOffIndexAbelianCorrection n) q := by
  exact ((C.phase_analytic q hq).differentiableAt.hasFDerivAt.fun_add
    (analyticOnNhd_hillHminusOffIndexAbelianCorrection n q hc).differentiableAt.hasFDerivAt).fderiv

theorem tendsto_completePhase_cotangent_sums (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hc : q ∈ hillHminusOffIndexAnalyticDomain) :
    Tendsto (fun N : ℕ => fderiv ℂ C.phase q+
      ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
        fderiv ℂ (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j) q) atTop
      (𝓝 (fderiv ℂ C.completePhase q)) := by
  rw [C.fderiv_completePhase_eq_add q hq hc]
  exact tendsto_const_nhds.add (tendsto_hillHminusOffIndexAbelian_cotangent_sums n q hc)

theorem completePhasePairBracket_eq_zero_at_all_endpoints
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) (hterminal : ∀ j : ℕ+, hillHminusDirichletSheet j q=0) :
    C.completePhasePairBracket D q=0 := by
  have hdir := C.source_subset_dirichlet hqC
  have hc := real_mem_hillHminusOffIndexAnalyticDomain q hr
  obtain ⟨a,ha⟩ := C.exists_fderiv_phase_eq_sheet_smul_at_endpoint q hqC (hterminal n)
  obtain ⟨b,hb⟩ := D.exists_fderiv_phase_eq_sheet_smul_at_endpoint q hqD (hterminal m)
  choose an han using (fun j => exists_fderiv_offIndexSignedTerm_eq_sheet_smul_at_endpoints n q hr hterminal j)
  choose am ham using (fun j => exists_fderiv_offIndexSignedTerm_eq_sheet_smul_at_endpoints m q hr hterminal j)
  have ha' : fderiv ℂ C.phase q=a • hillHminusSignedSheetCotangent q ((n:ℕ):ℤ) := by
    rw [hillHminusSignedSheetCotangent_apply_positive,ha]
  have hb' : fderiv ℂ D.phase q=b • hillHminusSignedSheetCotangent q ((m:ℕ):ℤ) := by
    rw [hillHminusSignedSheetCotangent_apply_positive,hb]
  have hfinite (N : ℕ) : NLS.Poisson.gardnerCotangentBivector
      (fderiv ℂ C.phase q+∑ j ∈ Finset.Icc (-(N:ℤ)) N,
        fderiv ℂ (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j) q)
      (fderiv ℂ D.phase q+∑ j ∈ Finset.Icc (-(N:ℤ)) N,
        fderiv ℂ (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm m p) j) q)=0 := by
    rw [ha',hb']
    simp only [han,ham,map_add,add_apply,map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul,
      hillHminusSignedSheetCotangents_Gardner_commute q hdir,mul_zero,Finset.sum_const_zero,add_zero]
  have hcont : Continuous (fun t : (PeriodOneHminusOne →L[ℂ] ℂ) × (PeriodOneHminusOne →L[ℂ] ℂ) =>
      NLS.Poisson.gardnerCotangentBivector t.1 t.2) := by fun_prop
  have ht := hcont.continuousAt.tendsto.comp
    ((C.tendsto_completePhase_cotangent_sums q hqC hc).prodMk_nhds
      (D.tendsto_completePhase_cotangent_sums q hqD hc))
  have hz : Tendsto (fun _ : ℕ => (0:ℂ)) atTop
      (𝓝 (NLS.Poisson.gardnerCotangentBivector (fderiv ℂ C.completePhase q) (fderiv ℂ D.completePhase q))) := by
    simpa only [Function.comp_def,hfinite] using ht
  change Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 (C.completePhasePairBracket D q)) at hz
  exact tendsto_nhds_unique hz tendsto_const_nhds

end NLS.KdV.HillPhysicalOnIndexPhaseChart
