import NLS.FunctionalAnalysis.RealSheetEndpoint
import NLS.KdV.HillGlobalIndexedSheet
import NLS.KdV.HillEndpointSheetFacts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every actual complete indexed Hill trajectory reaches an original periodic
endpoint in finite real time, with zero full sheet and zero log norming.
Collapsed gaps are included and no reachability premise is supplied. -/
theorem exists_hillGlobalIndexedCurve_periodicTerminal
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    ∃ t : ℝ,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff (γ t).val)
        (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk)=0 ∧
      (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk=
        hillRealLabels (γ 0).val (γ 0).property.1 (γ 0).property.2 (2*k-1) ∨
       hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk=
        hillRealLabels (γ 0).val (γ 0).property.1 (γ 0).property.2 (2*k)) ∧
      hillDirichletLogMultiplier (γ t).val (γ t).property.1 (γ t).property.2 k hk=0 := by
  let x : ℝ → ℝ := fun t => hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk
  let μ : ℝ → ℂ := fun t => x t
  let S : ℝ → ℂ := fun t => hillDirichletSheetRoot (SpectralWeight.one.toCoeff (γ t).val) (μ t)
  let Δ := hillL2Discriminant (SpectralWeight.one.toCoeff (γ 0).val)
  let a := hillRealLabels (γ 0).val (γ 0).property.1 (γ 0).property.2 (2*k-1)
  let b := hillRealLabels (γ 0).val (γ 0).property.1 (γ 0).property.2 (2*k)
  let v : ℝ → ℝ := fun t => (S t).re/2
  let F : ℝ → ℝ := fun y => (Δ (y:ℂ)*deriv Δ (y:ℂ)).re/4
  let G : ℝ → ℝ := fun y => ((Δ (y:ℂ)).re^2-4)/4
  have hΔreal (y : ℝ) : (Δ (y:ℂ)).im=0 :=
    hillL2Discriminant_real _ (γ 0).property.2 y
  have hΔderreal (y : ℝ) : (deriv Δ (y:ℂ)).im=0 :=
    hillL2Discriminant_deriv_real _ (γ 0).property.2 y
  have hSim (t : ℝ) : (S t).im=0 :=
    hillDirichletSheetRoot_at_dirichlet_real ⟨(γ t).val,(γ t).property⟩ k hk
  have hder (t : ℝ) : HasDerivAt μ (S t/2) t ∧
      HasDerivAt S (Δ (μ t)*deriv Δ (μ t)/2) t ∧ S t^2=Δ (μ t)^2-4 :=
    hillGlobalIndexedCurve_fixed_sheet_dynamics k hk γ hγ t
  have hx (t : ℝ) : x t∈Icc a b := by
    have hm := hillDirichletEnergy_mem_gap (γ t).val (γ t).property.1 (γ t).property.2 k hk
    have he := hillPeriodicEndpoints_eq_on_global_indexedCurve k k hk hk γ hγ t 0
    rwa [he.1,he.2] at hm
  have hxder (t : ℝ) : HasDerivAt x (v t) t := by
    simpa only [μ,Function.comp_def,Complex.reCLM_apply,div_ofNat_re,ofReal_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t).1
  have hvder (t : ℝ) : HasDerivAt v (F (x t)) t := by
    have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t).2.1).div_const 2
    apply hd.congr_deriv
    change ((Δ (μ t)*deriv Δ (μ t)/2).re)/2=F (x t)
    dsimp only [F,μ]
    simp only [div_ofNat_re]
    ring
  have hsheet (t : ℝ) : (v t)^2=G (x t) := by
    have hr := congrArg Complex.re (hder t).2.2
    simp only [μ,pow_two,mul_re,sub_re,hSim t,hΔreal (x t),mul_zero,sub_zero,
      show (4 : ℂ).re=4 from rfl] at hr
    dsimp only [v,G]
    nlinarith
  have hGend (y : ℝ) (hy : y∈Icc a b) (hz : G y=0) : y=a ∨ y=b := by
    by_contra hn
    push Not at hn
    have hi : y∈Ioo a b := ⟨lt_of_le_of_ne hy.1 hn.1.symm,lt_of_le_of_ne hy.2 hn.2⟩
    have hp := hillL2Radicand_pos_gap (γ 0).val (γ 0).property.1 (γ 0).property.2 k hk y hi
    rw [hillL2Radicand_re _ (γ 0).property.2] at hp
    change ((Δ (y:ℂ)).re^2-4)/4=0 at hz
    change 0<(Δ (y:ℂ)).re^2-4 at hp
    linarith
  have hSzero : ∃ t : ℝ, S t=0 := by
    have hab : a≤b := (hx 0).1.trans (hx 0).2
    rcases lt_or_eq_of_le hab with hopen | hcollapse
    · have hΔC : Continuous Δ := (analyticOnNhd_hillL2Discriminant _).continuous
      have hΔ'C : Continuous (deriv Δ) :=
        (analyticOnNhd_hillL2Discriminant _).deriv.continuous
      have hF : Continuous F :=
        (continuous_re.comp ((hΔC.comp continuous_ofReal).mul (hΔ'C.comp continuous_ofReal))).div_const 4
      have hG : Continuous G :=
        ((continuous_re.comp (hΔC.comp continuous_ofReal)).pow 2 |>.sub continuous_const).div_const 4
      have hnonzero := hillL2Discriminant_deriv_ne_zero_open_gap_endpoints
        ⟨(γ 0).val,(γ 0).property⟩ k hk hopen.ne
      have hzeros (y : ℝ) (hy : y∈Icc a b) (hy0 : G y=0) : F y≠0 := by
        have hdy : deriv Δ (y:ℂ)≠0 := by
          rcases hGend y hy hy0 with he | he
          · rw [he]; exact hnonzero.1
          · rw [he]; exact hnonzero.2
        have hdyre : (deriv Δ (y:ℂ)).re≠0 :=
          fun he => hdy (Complex.ext he (hΔderreal y))
        have hval : (Δ (y:ℂ)).re≠0 := by
          intro he
          change ((Δ (y:ℂ)).re^2-4)/4=0 at hy0
          rw [he] at hy0
          norm_num at hy0
        dsimp only [F]
        rw [mul_re,hΔreal y,hΔderreal y,mul_zero,sub_zero]
        exact div_ne_zero (mul_ne_zero hval hdyre) (by norm_num)
      obtain ⟨t,ht⟩ := exists_zero_velocity_of_bounded_sheetODE x v F G a b
        hxder hvder hx hsheet hF hG hzeros
      refine ⟨t,Complex.ext ?_ (hSim t)⟩
      change (S t).re/2=0 at ht
      change (S t).re=0
      linarith
    · refine ⟨0,?_⟩
      exact (hillDirichletSheetRoot_eq_zero_iff_logMultiplier_eq_zero
        ⟨(γ 0).val,(γ 0).property⟩ k hk).mpr
        (hillDirichletLogMultiplier_eq_zero_of_closed_gap
          (γ 0).val (γ 0).property.1 (γ 0).property.2 k hk hcollapse)
  obtain ⟨t,ht⟩ := hSzero
  have hG0 : G (x t)=0 := by rw [← hsheet t]; simp only [v,ht,zero_re,zero_div,zero_pow (by norm_num : 2≠0)]
  exact ⟨t,ht,hGend (x t) (hx t) hG0,
    (hillDirichletSheetRoot_eq_zero_iff_logMultiplier_eq_zero
      ⟨(γ t).val,(γ t).property⟩ k hk).mp ht⟩

end NLS.KdV
