import NLS.KdV.HillOnIndexActionVelocity
import NLS.ComplexAnalysis.ZeroFactorCotangent
import NLS.ComplexAnalysis.CosineEndpointCotangent

/-! At actual periodic terminals, full source cotangents of Abelian
values and on-index phases lie in their actual norming-sheet spans.
The moving divisor, half-gap, numerator and denominator derivatives
are accounted for before specializing the physical sheet to zero. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV
namespace HillProductEquationPatch

theorem analyticAt_terminalRootMultiplier (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    AnalyticAt ℂ (fun p => P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) p,p)) q :=
  (P.analytic_abelianGapRootMultiplier m _ ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩).comp
    (f := fun p : PeriodOneHminusOne => (P.physicalDirichletFrequency ((m:ℕ):ℤ) p,p))
    ((P.analytic_physicalDirichletFrequency ((m:ℕ):ℤ) q hq.1).prod analyticAt_id)

theorem exists_fderiv_physicalRootCoefficient_eq_sheet_smul
    (P : HillProductEquationPatch) (m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ P.physicalDirichletSource) (hzero : hillHminusDirichletSheet m q=0) :
    ∃ a : ℂ, fderiv ℂ (P.physicalDirichletRootCoefficient m) q=a • fderiv ℂ (hillHminusDirichletSheet m) q := by
  have he := fderiv_div_mul_of_zero (hillHminusDirichletSheet m)
    (fun p => P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) p,p))
    (fun _ => (1:ℂ)) q
    (analyticOnNhd_hillHminusDirichletSheet m q (P.source_subset_canonicalDirichlet hq.1)).differentiableAt
    (P.analyticAt_terminalRootMultiplier m q hq).differentiableAt (differentiableAt_const (1:ℂ))
    (P.abelianGapRootMultiplier_ne_zero m _ ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩) hzero
  simp only [mul_one] at he
  change fderiv ℂ (P.physicalDirichletRootCoefficient m) q = _ at he
  exact ⟨_,he⟩

theorem exists_fderiv_physicalOffIndexAbelianValue_eq_sheet_smul
    (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (hq : q ∈ P.physicalDirichletSource) (hzero : hillHminusDirichletSheet m q=0) :
    ∃ a : ℂ, fderiv ℂ (P.physicalOffIndexAbelianValue n m) q=a • fderiv ℂ (hillHminusDirichletSheet m) q := by
  have hH := (P.analytic_offIndexAbelianFilledQuotient n m hmn
    (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q) ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩).comp
      (f := fun p : PeriodOneHminusOne => (P.physicalDirichletFrequency ((m:ℕ):ℤ) p,p))
      ((P.analytic_physicalDirichletFrequency ((m:ℕ):ℤ) q hq.1).prod analyticAt_id)
  have he := fderiv_div_mul_of_zero (hillHminusDirichletSheet m)
    (fun p => P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) p,p))
    (fun p => P.offIndexAbelianFilledQuotient n m (P.physicalDirichletFrequency ((m:ℕ):ℤ) p,p)) q
    (analyticOnNhd_hillHminusDirichletSheet m q (P.source_subset_canonicalDirichlet hq.1)).differentiableAt
    (P.analyticAt_terminalRootMultiplier m q hq).differentiableAt hH.differentiableAt
    (P.abelianGapRootMultiplier_ne_zero m _ ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩) hzero
  change fderiv ℂ (P.physicalOffIndexAbelianValue n m) q = _ at he
  exact ⟨_,he⟩

theorem exists_fderiv_physicalOnIndexCorrection_eq_sheet_smul
    (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ P.physicalDirichletSource) (hzero : hillHminusDirichletSheet n q=0) :
    ∃ a : ℂ, fderiv ℂ (P.physicalOnIndexAbelianCorrection n) q=a • fderiv ℂ (hillHminusDirichletSheet n) q := by
  have hH := (P.analytic_onIndexAbelianFilledRemainder n
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q) ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩).comp
      (f := fun p : PeriodOneHminusOne => (P.physicalDirichletFrequency ((n:ℕ):ℤ) p,p))
      ((P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) q hq.1).prod analyticAt_id)
  have he := fderiv_div_mul_of_zero (hillHminusDirichletSheet n)
    (fun p => P.abelianGapRootMultiplier n (P.physicalDirichletFrequency ((n:ℕ):ℤ) p,p))
    (fun p => P.onIndexAbelianFilledRemainder n (P.physicalDirichletFrequency ((n:ℕ):ℤ) p,p)) q
    (analyticOnNhd_hillHminusDirichletSheet n q (P.source_subset_canonicalDirichlet hq.1)).differentiableAt
    (P.analyticAt_terminalRootMultiplier n q hq).differentiableAt hH.differentiableAt
    (P.abelianGapRootMultiplier_ne_zero n _ ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩) hzero
  change fderiv ℂ (P.physicalOnIndexAbelianCorrection n) q = _ at he
  exact ⟨_,he⟩

end HillProductEquationPatch
namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem exists_fderiv_phase_eq_sheet_smul_at_endpoint (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hzero : hillHminusDirichletSheet n q=0) :
    ∃ a : ℂ, fderiv ℂ C.phase q=a • fderiv ℂ (hillHminusDirichletSheet n) q := by
  obtain ⟨a,ha⟩ := P.exists_fderiv_physicalRootCoefficient_eq_sheet_smul n q (C.subset hq) hzero
  have hr0 : P.physicalDirichletRootCoefficient n q=0 := by
    simp only [HillProductEquationPatch.physicalDirichletRootCoefficient,hzero,zero_div]
  have hr : P.physicalDirichletRootCoefficient n =ᶠ[𝓝 q]
      (fun p => -I*C.halfGap p*Complex.sin (C.angle p)) := by
    filter_upwards [C.source_open.mem_nhds hq] with p hp
    exact (C.identities p hp).2.2.1.symm
  obtain ⟨b,hb⟩ := exists_fderiv_angle_eq_root_smul_at_zero_terminal C.halfGap C.angle
    (P.physicalDirichletRootCoefficient n) q (C.halfGap_analytic q hq).differentiableAt
    (C.angle_analytic q hq).differentiableAt (C.halfGap_ne q hq) hr0 hr
  obtain ⟨c,hc⟩ := P.exists_fderiv_physicalOnIndexCorrection_eq_sheet_smul n q (C.subset hq) hzero
  have he : C.phase =ᶠ[𝓝 q] (fun p => C.angle p-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n p) := by
    filter_upwards [C.source_open.mem_nhds hq] with p hp
    exact (C.identities p hp).2.2.2.2
  have hd := ((C.angle_analytic q hq).differentiableAt.hasFDerivAt.sub_const (Real.pi:ℂ)).fun_add
    (P.analytic_physicalOnIndexAbelianCorrection n q (C.subset hq)).differentiableAt.hasFDerivAt
  refine ⟨b*a+c,?_⟩
  rw [he.fderiv_eq,hd.fderiv,hb,ha,hc,smul_smul,← add_smul]

end HillPhysicalOnIndexPhaseChart

theorem exists_fderiv_hillHminusOffIndexAbelianValue_eq_sheet_smul_at_endpoint
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hzero : hillHminusDirichletSheet m q=0) :
    ∃ a : ℂ, fderiv ℂ (hillHminusPhysicalOffIndexAbelianValue n m) q=a • fderiv ℂ (hillHminusDirichletSheet m) q := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨r,hrpos,_,heq⟩ := exists_common_canonical_physical_Abelian_patch_ball P q hq hr
  have he : hillHminusPhysicalOffIndexAbelianValue n m =ᶠ[𝓝 q] P.physicalOffIndexAbelianValue n m := by
    filter_upwards [isOpen_ball.mem_nhds (show q ∈ ball q r from mem_ball_self hrpos)] with p hp
    exact heq n m hmn p hp
  rw [he.fderiv_eq]
  exact P.exists_fderiv_physicalOffIndexAbelianValue_eq_sheet_smul n m hmn q
    (P.real_mem_physicalDirichletSource q hq hr) hzero

end NLS.KdV
