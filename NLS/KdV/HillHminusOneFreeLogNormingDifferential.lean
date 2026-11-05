import NLS.KdV.HillHminusOneFreeNormingDifferential
import NLS.KdV.HillHminusOneDirichletLogNorming
import NLS.SequenceSpaces.PeriodOneHminusOneRealGerms
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # The exact Fourier derivative of the actual logarithmic norming germ

Agreement with actual real labels and norming factors identifies every
analytic logarithmic extension with the chart terminal logarithm as a
complex germ. Its derivative is (h_-n-h_n)/(4*i*pi*n), in the full
original complex H^-1 norm, with no support or reality restriction on h.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillHminusDirichletLogNorming_extension_fderiv_zero
    (K : PeriodOneHminusOne → ℂ) (hK : AnalyticAt ℂ K 0) (n : ℕ+)
    (hrec : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 (⟨0,by intro k; simp⟩ : PeriodOneRealHminusOne),
      K p.val = (hillHminusDirichletLogNorming p.val p.property n : ℂ))
    (h : PeriodOneHminusOne) :
    fderiv ℂ K 0 h = (h.val (-(n : ℤ))-h.val (n : ℤ))/(4*I*((n : ℂ)*(Real.pi : ℂ))) := by
  have hr0 : IsRealPeriodOneHminusOne 0 := by intro k; simp
  let q0 : PeriodOneRealHminusOne := ⟨0,hr0⟩
  obtain ⟨a,ha,haq,hroot,hmatch⟩ := exists_hillHminusDirichletEnergy_analytic_extension q0 n
  have ha0 : a 0 = (freeHillValue (n : ℕ) : ℂ) := by
    simpa only [q0,hillHminusDirichletEnergy_zero_potential] using haq
  let C := hillHminusMiuraChartAt 0
  have hC : (0 : PeriodOneHminusOne) ∈ C.domain := mem_hillHminusMiuraChartAt 0
  let β : PeriodOneHminusOne → ℂ := fun p => (-1 : ℂ)^(n : ℕ)*chartDirichletTerminalBranch C a p
  have hβ : AnalyticAt ℂ β 0 := analyticAt_const.mul (analyticAt_chartDirichletTerminalBranch C a 0 hC ha)
  have hγ0 : chartDirichletTerminalBranch C a 0 = (-1 : ℂ)^(n : ℕ) := by
    have he := hillHminusDirichletNorming_zero_potential hr0 n
    rw [hillHminusDirichletNorming,hillHminusDirichletEnergy_zero_potential] at he
    dsimp only [chartDirichletTerminalBranch]
    rw [ha0]
    exact he
  have hβ0 : β 0 = 1 := by
    dsimp only [β]
    rw [hγ0,← pow_two,← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]
    norm_num
  have hslit : β 0 ∈ Complex.slitPlane := by rw [hβ0]; exact Complex.one_mem_slitPlane
  let L : PeriodOneHminusOne → ℂ := fun p => Complex.log (β p)
  have hL : AnalyticAt ℂ L 0 := (analyticAt_clog hslit).comp (f := β) hβ
  have hdom : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q0, p.val ∈ C.domain :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (C.domain_open.mem_nhds hC)
  have heReal : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q0, K p.val = L p.val := by
    filter_upwards [hrec,hmatch,hdom] with p hp haP hpC
    rw [hp]
    change (hillHminusDirichletLogNorming p.val p.property n : ℂ) =
      Complex.log ((-1 : ℂ)^(n : ℕ)*chartDirichletTerminalBranch C a p.val)
    dsimp only [chartDirichletTerminalBranch]
    rw [haP,← hillHminusDirichletNorming_eq_chart C p.val hpC p.property n]
    exact (hillHminusDirichletLogNorming_eq_clog p.val p.property n).symm
  have hKL : K =ᶠ[𝓝 (0 : PeriodOneHminusOne)] L :=
    eventuallyEq_of_analyticAt_of_realHminus_agreement K L q0 hK hL heReal
  have hdL := hβ.differentiableAt.hasFDerivAt.clog hslit
  simp only [hβ0,inv_one,one_smul] at hdL
  have hdK : HasFDerivAt K (fderiv ℂ β 0) 0 := hdL.congr_of_eventuallyEq hKL
  rw [hdK.fderiv]
  exact chartDirichletTerminalBranch_signed_fderiv_zero C hC a ha n ha0 hroot h

end NLS.KdV
