import NLS.ZakharovShabat.SourceNormalizedWeightedActionPositive

/-! # The normalized action after the quadratic energy change

The energy half-gap is the frequency midpoint times the full frequency
gap. The correct normalized energy ratio is twice the first normalized
weighted action divided by the squared midpoint.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceStandardRootMidpoint_real_positive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hleft : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n).re) :
    ∃ t : ℝ, 0 < t ∧ sourceStandardRootMidpoint hp hp1 φ.val n = (t : ℂ) := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
  have hle : L.re ≤ R.re := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 n)
  obtain ⟨hLi,hRi⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
    (isRealType_periodOnePotential φ.val φ.property) n
  have hL : L = (L.re : ℂ) := Complex.ext rfl hLi
  have hR : R = (R.re : ℂ) := Complex.ext rfl hRi
  refine ⟨(L.re+R.re)/2,by change 0 < L.re at hleft; linarith,?_⟩
  change (L+R)/2 = _
  rw [hL,hR]
  push_cast
  rfl

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def normalizedEnergyActionRatio (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  2*C.normalizedWeightedAction n 1 ψ/(sourceStandardRootMidpoint hp hp1 ψ n)^2

theorem normalizedEnergyActionRatio_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUC : U ⊆ Metric.ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U)
    (hne : ∀ ψ ∈ U, sourceStandardRootMidpoint hp hp1 ψ n ≠ 0) :
    AnalyticOnNhd ℂ (C.normalizedEnergyActionRatio n) U := by
  have hN := C.normalizedWeightedAction_analytic U hU hUC n 1 hτ hγ
  intro ψ hψ
  exact (analyticAt_const.mul (hN ψ hψ)).div ((hτ ψ hψ).pow 2) (pow_ne_zero 2 (hne ψ hψ))

theorem normalizedEnergyActionRatio_factor
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (ψ : CoeffPair p) (A : ℂ)
    (hne : sourceStandardRootMidpoint hp hp1 ψ n ≠ 0)
    (hA : A = (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
      C.normalizedWeightedAction n 1 ψ) :
    2*A = (sourceStandardRootMidpoint hp hp1 ψ n*
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2*
        C.normalizedEnergyActionRatio n ψ := by
  rw [hA,normalizedEnergyActionRatio]
  field_simp

theorem normalizedEnergyActionRatio_real_positive
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ Metric.ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hleft : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n).re) :
    0 < (C.normalizedEnergyActionRatio n φ.val).re ∧
      (C.normalizedEnergyActionRatio n φ.val).im = 0 := by
  obtain ⟨t,ht,hτ⟩ := sourceStandardRootMidpoint_real_positive hp hp1 φ n hleft
  obtain ⟨hN,hNi⟩ := C.normalizedWeightedAction_one_real_positive φ hφ n hleft
  rw [normalizedEnergyActionRatio,hτ,← ofReal_pow]
  constructor
  · rw [div_ofReal_re]
    have hnum : (2*C.normalizedWeightedAction n 1 φ.val).re =
        2*(C.normalizedWeightedAction n 1 φ.val).re := by simp
    rw [hnum]
    exact div_pos (mul_pos (by norm_num) hN) (sq_pos_of_pos ht)
  · rw [div_ofReal_im]
    simp only [mul_im,show (2 : ℂ).re = 2 from rfl,show (2 : ℂ).im = 0 from rfl,
      hNi,mul_zero,zero_mul,add_zero,zero_div]

theorem normalizedEnergyActionRatio_analyticAt_of_real
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ Metric.ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hleft : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n).re) :
    AnalyticAt ℂ (C.normalizedEnergyActionRatio n) φ.val := by
  obtain ⟨r,hr,_,hN⟩ := C.exists_ball_normalizedWeightedActions (sourceHigherActionAtlas hp hp1) φ hφ
  obtain ⟨M,_,_,hreal,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨t,ht,hτ⟩ := sourceStandardRootMidpoint_real_positive hp hp1 φ n hleft
  have hne : sourceStandardRootMidpoint hp hp1 φ.val n ≠ 0 := by
    rw [hτ]
    exact ofReal_ne_zero.mpr ht.ne'
  exact (analyticAt_const.mul ((hN n 1).1 φ.val (Metric.mem_ball_self hr))).div
    (((hcoord φ.val (hreal φ.property) n).1).pow 2) (pow_ne_zero 2 hne)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
