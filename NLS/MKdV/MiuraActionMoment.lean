import NLS.MKdV.MiuraH1ActionSequence
import NLS.MKdV.MiuraActionDifferentialTrace

/-! # The convergent first physical mKdV action moment

The 2πn-weighted sum is a bounded linear functional on the actual native
action space. Composing with the full Banach analytic action sequence
constructs its analytic scalar realization, rather than differentiating
a formal coordinate series.
-/
noncomputable section
open Set Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

private theorem miuraActionMoment_symbol_bound (n : ℤ) :
    Weight.one n*‖2*(Real.pi : ℂ)*n‖ ≤ (2*Real.pi)*Weight.sobolev 3 n := by
  simp only [Weight.one_apply,one_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast,Weight.sobolev_apply,
    show (3 : ℝ) = (3 : ℕ) by norm_num,Real.rpow_natCast]
  have hx := abs_nonneg (n : ℝ)
  have hc := mul_nonneg (sq_nonneg |(n : ℝ)|) hx
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*Real.pi)
  nlinarith [sq_nonneg |(n : ℝ)|]

def miuraActionMomentSequence : WeightedCoeff (Weight.sobolev 3) 1 →L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry Weight.one 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM (Weight.sobolev 3) Weight.one
      (fun n => 2*(Real.pi : ℂ)*n) (2*Real.pi) (by positivity) miuraActionMoment_symbol_bound)

theorem miuraActionMomentSequence_apply (a : WeightedCoeff (Weight.sobolev 3) 1) (n : ℤ) :
    miuraActionMomentSequence a n = (2*(Real.pi : ℂ)*n)*a.val n := by
  change (1 : ℂ)*((2*(Real.pi : ℂ)*n)*a.val n) = _
  exact one_mul _

def miuraActionMomentFunctional : WeightedCoeff (Weight.sobolev 3) 1 →L[ℂ] ℂ :=
  (lp.tsumCLM ℂ ℤ ℂ).comp miuraActionMomentSequence

def miuraH1ActionMoment (a : ScalarDomain 2) : ℂ :=
  miuraActionMomentFunctional (miuraH1ActionSequence a)

theorem analyticAt_miuraH1ActionMoment (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : AnalyticAt ℂ miuraH1ActionMoment a := by
  obtain ⟨U,_,haU,hA,_⟩ := exists_local_miuraH1ActionSequence_domain a ha
  exact (miuraActionMomentFunctional.analyticAt _).comp (hA a haU)

/-- The bounded action moment is the literal convergent sum of the independent Hill actions. -/
theorem hasSum_miuraH1ActionMoment_physical (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*miuraMKdVAction a ha (n+1))
      (miuraH1ActionMoment a) := by
  let v := miuraH1ActionSequence a
  have hs : HasSum (fun n : ℤ => (2*(Real.pi : ℂ)*n)*v.val n) (miuraH1ActionMoment a) := by
    change HasSum _ (∑' n : ℤ, miuraActionMomentSequence v n)
    have hh := (miuraActionMomentSequence v).property.summable_of_one.hasSum
    change HasSum (fun n : ℤ => miuraActionMomentSequence v n) (∑' n : ℤ, miuraActionMomentSequence v n) at hh
    simpa only [miuraActionMomentSequence_apply] using hh
  have h := hs.nat_add_neg
  have hnonpos (n : ℕ) : v.val (-(n : ℤ)) = 0 := miuraH1ActionSequence_nonpositive a _ (by omega)
  have hz : v.val 0 = 0 := miuraH1ActionSequence_nonpositive a _ (by omega)
  simp only [hnonpos,hz,mul_zero,Int.cast_zero,add_zero] at h
  have hp := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one,Nat.cast_zero,Int.cast_zero,mul_zero,zero_mul,sub_zero] at hp
  convert! hp using 1
  funext n
  rw [miuraH1ActionSequence_physical a ha (n+1) (by omega)]
  norm_cast

/-- Every actual sequence derivative coordinate is the original scalar action derivative. -/
theorem fderiv_miuraH1ActionSequence_coordinate (a h : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((fderiv ℂ miuraH1ActionSequence a) h).val (n : ℤ) =
      (fderiv ℂ (miuraL2Action n) (scalarInclusion a)) (scalarInclusion h) := by
  obtain ⟨U,hU,haU,hA,hcoord⟩ := exists_local_miuraH1ActionSequence_domain a ha
  let ev := WeightedCoeff.evalCLM (Weight.sobolev 3) 1 (n : ℤ)
  have hd := (ev.hasFDerivAt.comp a (hA a haU).differentiableAt.hasFDerivAt).fderiv
  have he : (fun b => ev (miuraH1ActionSequence b)) =ᶠ[𝓝 a]
      (fun b => miuraL2Action n (scalarInclusion b)) := by
    filter_upwards [hU.mem_nhds haU] with b hb
    change (miuraH1ActionSequence b).val (n : ℤ) = _
    rw [hcoord b hb n hn,miuraComplexActionLevel,show 2*(1 : ℤ)-2 = 0 by norm_num,
      miuraL2Action,scalarL2Diagonal_scalarInclusion]
    rfl
  have hm := ((analyticOnNhd_miuraL2Action n hn _
    (real_mem_miuraL2ActionDomain _ (by intro j; simpa only [scalarInclusion_apply] using ha j))).differentiableAt.hasFDerivAt.comp
      a scalarInclusion.hasFDerivAt).fderiv
  have hv := congrArg (fun L : ScalarDomain 2 →L[ℂ] ℂ => L h)
    (hd.symm.trans (he.fderiv_eq.trans hm))
  exact hv

/-- The positive-index encoding also has zero nonpositive derivative coordinates. -/
theorem fderiv_miuraH1ActionSequence_nonpositive (a h : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℤ) (hn : ¬0 < n) :
    ((fderiv ℂ miuraH1ActionSequence a) h).val n = 0 := by
  obtain ⟨U,_,haU,hA,_⟩ := exists_local_miuraH1ActionSequence_domain a ha
  let ev := WeightedCoeff.evalCLM (Weight.sobolev 3) 1 n
  have hd := (ev.hasFDerivAt.comp a (hA a haU).differentiableAt.hasFDerivAt).fderiv
  have he : (fun b => ev (miuraH1ActionSequence b)) = (fun _ => 0) :=
    funext (fun b => miuraH1ActionSequence_nonpositive b n hn)
  change fderiv ℂ (fun b => ev (miuraH1ActionSequence b)) a = _ at hd
  rw [he,fderiv_fun_const] at hd
  exact (congrArg (fun L : ScalarDomain 2 →L[ℂ] ℂ => L h) hd).symm

private theorem hasSum_positive_of_nonpositive_zero (f : ℤ → ℂ) (z : ℂ)
    (hs : HasSum f z) (hz : ∀ n : ℤ, ¬0 < n → f n = 0) :
    HasSum (fun n : ℕ => f (n+1)) z := by
  have h := hs.nat_add_neg
  have hneg (n : ℕ) : f (-(n : ℤ)) = 0 := hz _ (by omega)
  have hzero : f 0 = 0 := hz _ (by omega)
  simp only [hneg,hzero,add_zero] at h
  have hshift := (hasSum_nat_add_iff' 1).mpr h
  simpa only [Finset.sum_range_one,Nat.cast_zero,hzero,sub_zero,Nat.cast_add,Nat.cast_one] using hshift

/-- The actual scalar derivative is an absolutely convergent action-cotangent sum. -/
theorem hasSum_fderiv_miuraH1ActionMoment (a h : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*
      (fderiv ℂ (miuraL2Action (n+1)) (scalarInclusion a)) (scalarInclusion h))
      (fderiv ℂ miuraH1ActionMoment a h) := by
  obtain ⟨U,_,haU,hA,_⟩ := exists_local_miuraH1ActionSequence_domain a ha
  have hd := (miuraActionMomentFunctional.hasFDerivAt.comp a
    (hA a haU).differentiableAt.hasFDerivAt).fderiv
  let v := (fderiv ℂ miuraH1ActionSequence a) h
  have hs : HasSum (fun n : ℤ => (2*(Real.pi : ℂ)*n)*v.val n) (miuraActionMomentFunctional v) := by
    change HasSum _ (∑' n : ℤ, miuraActionMomentSequence v n)
    have hh := (miuraActionMomentSequence v).property.summable_of_one.hasSum
    change HasSum (fun n : ℤ => miuraActionMomentSequence v n) (∑' n : ℤ, miuraActionMomentSequence v n) at hh
    simpa only [miuraActionMomentSequence_apply] using hh
  have hp := hasSum_positive_of_nonpositive_zero _ _ hs (fun n hn => by
    rw [show v.val n = 0 from fderiv_miuraH1ActionSequence_nonpositive a h ha n hn,mul_zero])
  have htarget : fderiv ℂ miuraH1ActionMoment a h = miuraActionMomentFunctional v :=
    congrArg (fun L : ScalarDomain 2 →L[ℂ] ℂ => L h) hd
  rw [htarget]
  convert! hp using 1
  funext n
  rw [show (n : ℤ)+1 = ((n+1 : ℕ) : ℤ) by omega]
  rw [show v.val (n+1 : ℕ) = _ from fderiv_miuraH1ActionSequence_coordinate a h ha (n+1) (by omega)]
  norm_cast

/-- Actual differentiation of the native weighted sum recovers every nonconstant mass mode. -/
theorem fderiv_miuraH1ActionMoment_scalarMode (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (k : ℤ) (hk : k ≠ 0) :
    fderiv ℂ miuraH1ActionMoment a (scalarMode k 1) = a.val (-k) := by
  have h := hasSum_fderiv_miuraH1ActionMoment a (scalarMode k 1) ha
  rw [scalarInclusion_scalarMode] at h
  have hg := hasSum_miuraActionDifferentials_fourier a ha (-k) (neg_ne_zero.mpr hk)
  simp only [neg_neg] at hg
  exact h.unique hg

end NLS.MKdV
