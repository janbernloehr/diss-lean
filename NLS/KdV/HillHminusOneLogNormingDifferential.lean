import NLS.KdV.HillHminusOneNormingDifferential
import NLS.KdV.HillHminusOneDirichletLogNorming
import NLS.SequenceSpaces.PeriodOneHminusOneRealGerms
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Exact logarithmic norming differentials at every real H^-1 potential

Real-form uniqueness identifies any actual analytic logarithmic extension
with the chart terminal logarithm. Its derivative is the original
potential pairing minus the Dirichlet energy overlap correction.
No gap openness, support restriction or reality of the direction is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusDirichletLogNorming_extension_fderiv_eq_terminal
    (K : PeriodOneHminusOne → ℂ) (q : PeriodOneRealHminusOne) (hK : AnalyticAt ℂ K q.val) (n : ℕ+)
    (hrec : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
      K p.val = (hillHminusDirichletLogNorming p.val p.property n : ℂ))
    (C : HillHminusMiuraChart) (hC : q.val ∈ C.domain)
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a q.val)
    (haq : a q.val = (hillHminusDirichletEnergy q.val q.property n : ℂ))
    (hmatch : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
      a p.val = (hillHminusDirichletEnergy p.val p.property n : ℂ))
    (h : PeriodOneHminusOne) :
    fderiv ℂ K q.val h = (chartDirichletTerminalBranch C a q.val)⁻¹*
      fderiv ℂ (chartDirichletTerminalBranch C a) q.val h := by
  let s : ℂ := (-1)^(n : ℕ)
  let b := chartDirichletTerminalBranch C a
  let β : PeriodOneHminusOne → ℂ := fun p => s*b p
  have hb : AnalyticAt ℂ b q.val := analyticAt_chartDirichletTerminalBranch C a q.val hC ha
  have hβ : AnalyticAt ℂ β q.val := analyticAt_const.mul hb
  have hbq : b q.val = hillHminusDirichletNorming q.val q.property n := by
    dsimp only [b,chartDirichletTerminalBranch]
    rw [haq,← hillHminusDirichletNorming_eq_chart C q.val hC q.property n]
  have hslit : β q.val ∈ Complex.slitPlane := by
    dsimp only [β,s]
    rw [hbq,hillHminusDirichletNorming_signed_eq_real]
    exact Complex.ofReal_mem_slitPlane.mpr (hillHminusDirichletNorming_signed_pos q.val q.property n)
  let L : PeriodOneHminusOne → ℂ := fun p => Complex.log (β p)
  have hL : AnalyticAt ℂ L q.val := (analyticAt_clog hslit).comp (f := β) hβ
  have hdom : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q, p.val ∈ C.domain :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (C.domain_open.mem_nhds hC)
  have heReal : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q, K p.val = L p.val := by
    filter_upwards [hrec,hmatch,hdom] with p hp haP hpC
    rw [hp]
    change (hillHminusDirichletLogNorming p.val p.property n : ℂ) =
      Complex.log ((-1 : ℂ)^(n : ℕ)*chartDirichletTerminalBranch C a p.val)
    dsimp only [chartDirichletTerminalBranch]
    rw [haP,← hillHminusDirichletNorming_eq_chart C p.val hpC p.property n]
    exact (hillHminusDirichletLogNorming_eq_clog p.val p.property n).symm
  have hKL : K =ᶠ[𝓝 q.val] L :=
    eventuallyEq_of_analyticAt_of_realHminus_agreement K L q hK hL heReal
  have hdL := (hb.differentiableAt.hasFDerivAt.const_mul s).clog hslit
  have hdK := hdL.congr_of_eventuallyEq hKL
  have hd := congrArg (fun T : PeriodOneHminusOne →L[ℂ] ℂ => T h) hdK.fderiv
  simp only [smul_apply,smul_eq_mul] at hd
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hbn : b q.val ≠ 0 := hbq ▸ hillHminusDirichletNorming_ne_zero q.val q.property n
  rw [hd]
  change (s*b q.val)⁻¹*(s*fderiv ℂ b q.val h) = (b q.val)⁻¹*fderiv ℂ b q.val h
  field_simp

theorem hillHminusDirichletLogNorming_extension_differential
    (K : PeriodOneHminusOne → ℂ) (q : PeriodOneRealHminusOne) (hK : AnalyticAt ℂ K q.val) (n : ℕ+)
    (hrec : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
      K p.val = (hillHminusDirichletLogNorming p.val p.property n : ℂ))
    (C : HillHminusMiuraChart) (hC : q.val ∈ C.domain)
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a q.val)
    (haq : a q.val = (hillHminusDirichletEnergy q.val q.property n : ℂ))
    (hroot : ∀ᶠ p in 𝓝 q.val, hillHminusDirichlet p (a p) = 0)
    (hmatch : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
      a p.val = (hillHminusDirichletEnergy p.val p.property n : ℂ))
    (h : PeriodOneHminusOne) :
    fderiv ℂ K q.val h =
      hillHminusWeakPotential h (hillHminusDirichletColumn q.val (a q.val)) (C.physicalPosition q.val (a q.val) (1,0))-
        fderiv ℂ a q.val h*(∫ s in (0 : ℝ)..1,
          extend (hillHminusDirichletColumn q.val (a q.val)) s*extend (C.physicalPosition q.val (a q.val) (1,0)) s) := by
  have hz : hillHminusDirichlet q.val (a q.val) = 0 := by
    rw [haq]
    exact hillHminusDirichletEnergy_zero q.val q.property n
  have hrecip := C.dirichlet_cosine_terminal_reciprocal q.val hC (a q.val) hz
  have hbn : chartDirichletTerminalBranch C a q.val ≠ 0 := by
    dsimp only [chartDirichletTerminalBranch]
    rw [haq,← hillHminusDirichletNorming_eq_chart C q.val hC q.property n]
    exact hillHminusDirichletNorming_ne_zero q.val q.property n
  have hc : extend (C.physicalPosition q.val (a q.val) (1,0)) 1 =
      (chartDirichletTerminalBranch C a q.val)⁻¹ := by
    apply mul_right_cancel₀ hbn
    rw [inv_mul_cancel₀ hbn]
    exact hrecip
  rw [hillHminusDirichletLogNorming_extension_fderiv_eq_terminal K q hK n hrec C hC a ha haq hmatch h,← hc]
  exact chartDirichletTerminalBranch_relative_differential C q.val hC a ha hz hroot h

end NLS.KdV
