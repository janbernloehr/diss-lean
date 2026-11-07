import NLS.ComplexAnalysis.AnalyticRadicandEquation
import NLS.ComplexAnalysis.AnalyticQuotientUniqueness

/-! Analytic even/odd branch systems are uniquely normalized by their
even value at a SIMPLE radicand zero. The conserved square identity
and the odd analytic order of the radicand exclude a nonzero analytic
homogeneous pair. No square-root choice is required. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem analytic_branch_system_zero (D f A B : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ)
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (ha : a ∈ Ω)
    (hD : AnalyticOnNhd ℂ D Ω) (hDa : D a = 0) (hDprime : deriv D a ≠ 0)
    (hA : AnalyticOnNhd ℂ A Ω) (hB : AnalyticOnNhd ℂ B Ω) (hAa : A a = 0)
    (heA : ∀ z ∈ Ω, deriv A z = f z*B z)
    (heB : ∀ z ∈ Ω, D z*deriv B z+(deriv D z/2)*B z = f z*A z) :
    ∀ z ∈ Ω, A z = 0 ∧ B z = 0 := by
  let K : ℂ → ℂ := fun z => (A z)^2-D z*(B z)^2
  have hKa : K a = 0 := by simp only [K,hAa,hDa,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,sub_self]
  have hKd (z : ℂ) (hz : z ∈ Ω) : HasDerivAt K 0 z := by
    have hd := ((hA z hz).differentiableAt.hasDerivAt.pow 2).sub
      ((hD z hz).differentiableAt.hasDerivAt.fun_mul ((hB z hz).differentiableAt.hasDerivAt.pow 2))
    convert! hd using 1
    simp only [Pi.pow_apply,Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one]
    linear_combination -2*A z*(heA z hz)+2*B z*(heB z hz)
  have hKzero (z : ℂ) (hz : z ∈ Ω) : K z = 0 := by
    rw [← hKa]
    exact hΩ.is_const_of_deriv_eq_zero hconn
      (fun z hz => (hKd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hKd z hz).deriv) hz ha
  have hsquare (z : ℂ) (hz : z ∈ Ω) : (A z)^2 = D z*(B z)^2 := sub_eq_zero.mp (hKzero z hz)
  have hBtop : analyticOrderAt B a = ⊤ := by
    by_contra hBfin
    have he : A^2 =ᶠ[𝓝 a] D*B^2 := by
      filter_upwards [hΩ.mem_nhds ha] with z hz
      exact hsquare z hz
    have ho := analyticOrderAt_congr he
    rw [analyticOrderAt_pow (hA a ha),analyticOrderAt_mul (hD a ha) ((hB a ha).pow 2),
      analyticOrderAt_pow (hB a ha),(hD a ha).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hDa hDprime] at ho
    simp only [nsmul_eq_mul] at ho
    lift analyticOrderAt B a to ℕ using hBfin with k hk
    by_cases hAfin : analyticOrderAt A a = ⊤
    · rw [hAfin] at ho
      have hne : (1:ℕ∞)+2*(k:ℕ∞) ≠ ⊤ := by
        exact ENat.natCast_ne_top (1+2*k)
      exact hne ho.symm
    · lift analyticOrderAt A a to ℕ using hAfin with j hj
      have hn := congrArg ENat.toNat ho
      rw [ENat.toNat_add (m := 1) (n := ((2:ℕ):ℕ∞)*(k:ℕ∞)) (by norm_num) (by exact ENat.natCast_ne_top (2*k))] at hn
      simp only [ENat.toNat_mul,ENat.toNat_one,ENat.toNat_natCast] at hn
      omega
  have hBzero : EqOn B 0 Ω := (hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn ha (analyticOrderAt_eq_top.mp hBtop))
  intro z hz
  have hBz : B z = 0 := hBzero hz
  refine ⟨?_,hBz⟩
  apply eq_zero_of_pow_eq_zero
  simpa only [hBz,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] using hsquare z hz

theorem analytic_branch_system_unique (D f A B C E : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ)
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (ha : a ∈ Ω)
    (hD : AnalyticOnNhd ℂ D Ω) (hDa : D a = 0) (hDprime : deriv D a ≠ 0)
    (hA : AnalyticOnNhd ℂ A Ω) (hB : AnalyticOnNhd ℂ B Ω)
    (hC : AnalyticOnNhd ℂ C Ω) (hE : AnalyticOnNhd ℂ E Ω) (hbase : A a = C a)
    (heA : ∀ z ∈ Ω, deriv A z = f z*B z)
    (heB : ∀ z ∈ Ω, D z*deriv B z+(deriv D z/2)*B z = f z*A z)
    (heC : ∀ z ∈ Ω, deriv C z = f z*E z)
    (heE : ∀ z ∈ Ω, D z*deriv E z+(deriv D z/2)*E z = f z*C z) :
    ∀ z ∈ Ω, A z = C z ∧ B z = E z := by
  have hsubA (z : ℂ) (hz : z ∈ Ω) : deriv (fun w => A w-C w) z = deriv A z-deriv C z :=
    ((hA z hz).differentiableAt.hasDerivAt.sub (hC z hz).differentiableAt.hasDerivAt).deriv
  have hsubB (z : ℂ) (hz : z ∈ Ω) : deriv (fun w => B w-E w) z = deriv B z-deriv E z :=
    ((hB z hz).differentiableAt.hasDerivAt.sub (hE z hz).differentiableAt.hasDerivAt).deriv
  have hzero := analytic_branch_system_zero D f (fun z => A z-C z) (fun z => B z-E z) Ω a
    hΩ hconn ha hD hDa hDprime (hA.sub hC) (hB.sub hE) (sub_eq_zero.mpr hbase) (by
      intro z hz
      rw [hsubA z hz]
      linear_combination heA z hz-heC z hz) (by
      intro z hz
      rw [hsubB z hz]
      linear_combination heB z hz-heE z hz)
  exact fun z hz => ⟨sub_eq_zero.mp (hzero z hz).1,sub_eq_zero.mp (hzero z hz).2⟩

theorem continuousAt_zero_of_off_analytic_zeros {E : Type*} [NormedAddCommGroup E]
    (Q : ℂ → ℂ) (F : ℂ → E) (z : ℂ) (hQ : AnalyticAt ℂ Q z)
    (hfinite : analyticOrderAt Q z ≠ ⊤) (hF : ContinuousAt F z)
    (heq : ∀ᶠ w in 𝓝[≠] z, Q w ≠ 0 → F w = 0) : F z = 0 := by
  have hz : ∀ᶠ w in 𝓝[≠] z, F w = 0 := by
    filter_upwards [eventually_ne_zero_of_finite_analyticOrder hQ hfinite,heq] with w hw he
    exact he hw
  have hzero : Tendsto F (𝓝[≠] z) (𝓝 0) := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (show F =ᶠ[𝓝[≠] z] (fun _ => 0) from hz))
  exact tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds) hzero

end NLS.ComplexAnalysis
