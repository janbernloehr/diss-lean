import NLS.ComplexAnalysis.ParametricDividedDifference

/-! # Uniqueness of continuous germs of simple spectral roots

A moving divided difference is nonzero at the simple root. Its exact
factorization identifies any other continuous root branch through that point.
Only the reference branch needs to be analytic.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem eventuallyEq_of_simple_spectral_root
    (F : ℂ × A → ℂ) (a b : A → ℂ) {V : Set A} (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) (ha : AnalyticOnNhd ℂ a V)
    (q : A) (hq : q ∈ V) (hb : ContinuousAt b q) (he : b q = a q)
    (hs : deriv (fun z => F (z,q)) (a q) ≠ 0)
    (hzeroA : ∀ᶠ p in 𝓝 q, F (a p,p) = 0)
    (hzeroB : ∀ᶠ p in 𝓝 q, F (b p,p) = 0) :
    b =ᶠ[𝓝 q] a := by
  let Q := parametricMovingDividedDifference F a
  have hQa := analyticOnNhd_parametricMovingDividedDifference F a hV hF ha
  have hcont : ContinuousAt (fun p => Q (b p,p)) q :=
    (hQa (b q,q) ⟨mem_univ _,hq⟩).continuousAt.comp (f := fun p => (b p,p)) (hb.prodMk continuousAt_id)
  have hn : Q (b q,q) ≠ 0 := by
    rw [he]
    change parametricMovingDividedDifference F a (a q,q) ≠ 0
    rw [parametricMovingDividedDifference_center F a hF q hq]
    exact hs
  filter_upwards [hcont.eventually_ne hn,hzeroA,hzeroB,hV.mem_nhds hq] with p hp ha0 hb0 hpV
  have hf := parametricMovingDividedDifference_mul F a hF ha (b p) p hpV
  rw [hb0,ha0,sub_self] at hf
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp)

end NLS.ComplexAnalysis
