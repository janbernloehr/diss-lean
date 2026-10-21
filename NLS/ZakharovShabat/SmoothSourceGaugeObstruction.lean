import NLS.Dynamics.VariableAmplitudePhaseObstruction
import NLS.ZakharovShabat.SmoothSourceMassDivergence
import NLS.ZakharovShabat.AnalyticNLSWellposedness
import NLS.ZakharovShabat.SmoothClassicalNLSNonextension
import NLS.ZakharovShabat.SourceSection18GaugeCorrection

noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The physical mass gauge relates actual Fourier coefficients at any two exponents. -/
theorem SmoothNLSData.ordinarySource_fst_eq_gauged_renormalized
    (f : SmoothNLSData) (time : ℝ) (n : ℤ) :
    (f.ordinarySource q time).val.fst n =
      Complex.exp (-((4*classicalNLSMass f.value*time : ℝ) : ℂ)*Complex.I)*
        (f.renormalizedSource p time).val.fst n := by
  simp only [SmoothNLSData.ordinarySource,SmoothNLSData.renormalizedSource,
    smoothPeriodOneSourceAt_fst,f.renormalized_phase time,ContinuousMap.smul_apply,smul_eq_mul]
  unfold periodOneCoefficient
  rw [fourierCoeffOn.const_mul _ _ n (by norm_num),neg_mul,Complex.exp_neg,
    ← mul_assoc,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_mul]

/-- Local analytic renormalized solutions and the physical gauge obstruct ordinary
source extensions into every sequence exponent, including infinity. -/
theorem smooth_source_nonextension_of_local_renormalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (hlocal : IsLocallyAnalyticallyWellposed (fun f : SmoothNLSData => f.renormalizedSource p))
    (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (0 : ℝ) T) F) :
    ¬ ContinuousAt F φ := by
  intro hcont
  obtain ⟨S,hS,U,hU,hφU,L,hL,G,hG,hGL⟩ := hlocal φ
  obtain ⟨f,hf⟩ := exists_smoothNLSData_sequence hp hp1 φ
  have hex : ∃ n : ℤ, φ.val.fst n ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    rw [mem_sourceHilbertLocus_iff]
    simp only [h,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    exact summable_zero
  obtain ⟨n,hn⟩ := hex
  let d := min T S
  have hd : 0 < d := lt_min hT hS
  let intoT : C(Icc (0 : ℝ) d,Icc (0 : ℝ) T) :=
    ⟨fun τ => ⟨τ.val,τ.property.1,τ.property.2.trans (min_le_left _ _)⟩,by fun_prop⟩
  let intoS : C(Icc (0 : ℝ) d,Icc (-S) S) :=
    ⟨fun τ => ⟨τ.val,by
      constructor
      · linarith [τ.property.1]
      · exact τ.property.2.trans (min_le_right _ _)⟩,by fun_prop⟩
  let cp : C(realTypeSourceSubmodule p,ℂ) :=
    ⟨fun ξ => ξ.val.fst n,(lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp
      ((CoeffPair.toMax p).continuous.fst.comp continuous_subtype_val)⟩
  let cq : C(realTypeSourceSubmodule q,ℂ) :=
    ⟨fun ξ => ξ.val.fst n,(lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).continuous.comp
      ((CoeffPair.toMax q).continuous.fst.comp continuous_subtype_val)⟩
  let r := fun j => cp.comp ((G ((f j).source p)).comp intoS)
  let R := cp.comp ((G φ).comp intoS)
  let g := fun j => cq.comp ((F ((f j).source p)).comp intoT)
  let H := cq.comp ((F φ).comp intoT)
  have hr : Tendsto r atTop (𝓝 R) :=
    (ContinuousMap.continuous_postcomp cp).continuousAt.tendsto.comp
      ((ContinuousMap.continuous_precomp intoS).continuousAt.tendsto.comp
        ((hG φ hφU).continuousAt.tendsto.comp hf))
  have hg : Tendsto g atTop (𝓝 H) :=
    (ContinuousMap.continuous_postcomp cq).continuousAt.tendsto.comp
      ((ContinuousMap.continuous_precomp intoT).continuousAt.tendsto.comp
        (hcont.tendsto.comp hf))
  have hR : R ⟨0,le_rfl,hd.le⟩ ≠ 0 := by
    change (G φ (intoS ⟨0,le_rfl,hd.le⟩)).val.fst n ≠ 0
    rw [hGL φ hφU]
    change (L φ 0).val.fst n ≠ 0
    rw [(hL φ hφU).initial]
    exact hn
  have hsmooth (f' : SmoothNLSData) (hu : f'.source p ∈ U) (τ : Icc (-S) S) :
      G (f'.source p) τ = f'.renormalizedSource p τ.val := by
    rw [hGL _ hu]
    exact tendsto_nhds_unique
      ((hL _ hu).approximation (fun _ : ℕ => f') tendsto_const_nhds τ.val τ.property)
      tendsto_const_nhds
  have he : ∀ᶠ j in atTop, ∀ τ : Icc (0 : ℝ) d,
      g j τ = Complex.exp (-((τ.val*(4*classicalNLSMass (f j).value) : ℝ) : ℂ)*Complex.I)*r j τ := by
    filter_upwards [hf.eventually (hU.mem_nhds hφU)] with j hj
    intro τ
    change (F ((f j).source p) (intoT τ)).val.fst n =
      _*(G ((f j).source p) (intoS τ)).val.fst n
    rw [hF,hsmooth (f j) hj]
    simpa only [intoT,intoS,ContinuousMap.coe_mk,mul_comm τ.val]
      using (f j).ordinarySource_fst_eq_gauged_renormalized (p := p) (q := q) τ.val n
  exact NLS.Dynamics.not_tendsto_modulated_trajectories d hd
    (fun j => 4*classicalNLSMass (f j).value)
    ((tendsto_smoothNLSData_mass_atTop h2p φ hφ f hf).const_mul_atTop (by norm_num))
    r R hr hR g he H hg

end NLS.ZakharovShabat
