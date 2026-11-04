import NLS.KdV.HillHminusOneDirichletNorming
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Intrinsic logarithmic Dirichlet norming data in original H^-1

The signed actual endpoint factor is strictly positive, fixing the real
logarithm without a phase ambiguity. Its local complex analytic extension
uses the principal logarithm only near this positive value. The norming
logarithm is zero at every collapsed gap and at the free potential.
Sequence-valued estimates and the global inverse remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

def hillHminusDirichletLogNorming (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : ℝ :=
  Real.log ((-1 : ℝ)^(n : ℕ)*(hillHminusDirichletNorming q hr n).re)

theorem hillHminusDirichletNorming_signed_eq_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (-1 : ℂ)^(n : ℕ)*hillHminusDirichletNorming q hr n =
      (((-1 : ℝ)^(n : ℕ)*(hillHminusDirichletNorming q hr n).re : ℝ) : ℂ) := by
  have hs : (-1 : ℂ)^(n : ℕ) = (((-1 : ℝ)^(n : ℕ) : ℝ) : ℂ) := by simp
  rw [hs]
  apply Complex.ext <;> simp [hillHminusDirichletNorming_real q hr n]

theorem hillHminusDirichletLogNorming_eq_clog (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    Complex.log ((-1 : ℂ)^(n : ℕ)*hillHminusDirichletNorming q hr n) =
      (hillHminusDirichletLogNorming q hr n : ℂ) := by
  rw [hillHminusDirichletNorming_signed_eq_real]
  exact (Complex.ofReal_log (hillHminusDirichletNorming_signed_pos q hr n).le).symm

theorem exp_hillHminusDirichletLogNorming (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    Real.exp (hillHminusDirichletLogNorming q hr n) =
      (-1 : ℝ)^(n : ℕ)*(hillHminusDirichletNorming q hr n).re :=
  Real.exp_log (hillHminusDirichletNorming_signed_pos q hr n)

theorem hillHminusDirichletLogNorming_zero_of_norming_eq_sign
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (h : hillHminusDirichletNorming q hr n = (-1 : ℂ)^(n : ℕ)) :
    hillHminusDirichletLogNorming q hr n = 0 := by
  have hs : (-1 : ℂ)^(n : ℕ) = (((-1 : ℝ)^(n : ℕ) : ℝ) : ℂ) := by simp
  have hs₂ : ((-1 : ℝ)^(n : ℕ))^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]
    norm_num
  rw [hillHminusDirichletLogNorming,h,hs,ofReal_re,← pow_two,hs₂,Real.log_one]

theorem hillHminusDirichletLogNorming_zero_of_closed_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hclosed : hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ))) :
    hillHminusDirichletLogNorming q hr n = 0 :=
  hillHminusDirichletLogNorming_zero_of_norming_eq_sign q hr n
    (hillHminusDirichletNorming_eq_sign_of_closed_gap q hr n hclosed)

theorem hillHminusDirichletLogNorming_zero_potential (hr : IsRealPeriodOneHminusOne 0) (n : ℕ+) :
    hillHminusDirichletLogNorming 0 hr n = 0 :=
  hillHminusDirichletLogNorming_zero_of_norming_eq_sign 0 hr n (hillHminusDirichletNorming_zero_potential hr n)

theorem exists_hillHminusDirichletLogNorming_analytic_extension (q : PeriodOneRealHminusOne) (n : ℕ+) :
    ∃ L : PeriodOneHminusOne → ℂ, AnalyticAt ℂ L q.val ∧
      L q.val = (hillHminusDirichletLogNorming q.val q.property n : ℂ) ∧
      ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
        L p.val = (hillHminusDirichletLogNorming p.val p.property n : ℂ) := by
  obtain ⟨b,hb,hbq,hmatch⟩ := exists_hillHminusDirichletNorming_analytic_extension q n
  let L : PeriodOneHminusOne → ℂ := fun p => Complex.log ((-1 : ℂ)^(n : ℕ)*b p)
  have ha : AnalyticAt ℂ (fun p => (-1 : ℂ)^(n : ℕ)*b p) q.val := analyticAt_const.mul hb
  have hslit : (-1 : ℂ)^(n : ℕ)*b q.val ∈ Complex.slitPlane := by
    rw [hbq,hillHminusDirichletNorming_signed_eq_real]
    exact Complex.ofReal_mem_slitPlane.mpr (hillHminusDirichletNorming_signed_pos q.val q.property n)
  refine ⟨L,(analyticAt_clog hslit).comp
    (f := fun p : PeriodOneHminusOne => (-1 : ℂ)^(n : ℕ)*b p) ha,?_,?_⟩
  · change Complex.log ((-1 : ℂ)^(n : ℕ)*b q.val) = _
    rw [hbq,hillHminusDirichletLogNorming_eq_clog]
  filter_upwards [hmatch] with p hp
  change Complex.log ((-1 : ℂ)^(n : ℕ)*b p.val) = _
  rw [hp,hillHminusDirichletLogNorming_eq_clog]

theorem continuous_hillHminusDirichletLogNorming (n : ℕ+) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusDirichletLogNorming q.val q.property n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨L,hL,_,he⟩ := exists_hillHminusDirichletLogNorming_analytic_extension q n
  have heq : (fun p : PeriodOneRealHminusOne => (hillHminusDirichletLogNorming p.val p.property n : ℂ)) =ᶠ[𝓝 q]
      (fun p : PeriodOneRealHminusOne => L p.val) := he.mono (fun _ hp => hp.symm)
  have hc : ContinuousAt (fun p : PeriodOneRealHminusOne => (hillHminusDirichletLogNorming p.val p.property n : ℂ)) q :=
    (hL.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq heq
  have hcre := Complex.continuous_re.continuousAt.comp hc
  simpa only [Function.comp_def,ofReal_re] using! hcre

end NLS.KdV
