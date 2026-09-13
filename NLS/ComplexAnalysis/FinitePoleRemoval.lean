import NLS.ComplexAnalysis.LogDerivativeLocal
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Removing the finitely many logarithmic-derivative poles

Subtract the analytic multiplicity divided by the centered coordinate at
each zero. Normal form fills the removable values and yields an analytic
function on the whole set, equal to the remainder away from the poles.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- Normal form fills a removable meromorphic germ using any analytic representative. -/
theorem analyticAt_normalForm_of_punctured_eq {F g : ℂ → ℂ} {K : Set ℂ} {c : ℂ}
    (hF : MeromorphicOn F K) (hc : c ∈ K) (hg : AnalyticAt ℂ g c)
    (he : F =ᶠ[𝓝[≠] c] g) : AnalyticAt ℂ (toMeromorphicNFOn F K) c := by
  have hnf := meromorphicNFOn_toMeromorphicNFOn F K hc
  have he' := (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg.meromorphicNFAt).mp
    ((hF.toMeromorphicNFOn_eq_self_on_nhdsNE hc).trans he)
  exact hg.congr he'.symm

/-- The finite principal-part sum of a logarithmic derivative. -/
def logDerivPrincipalParts (f : ℂ → ℂ) (s : Finset ℂ) (z : ℂ) : ℂ :=
  ∑ a ∈ s, (analyticOrderNatAt f a : ℂ)/(z-a)

/-- The principal-part sum is analytic away from its finite set of poles. -/
theorem analyticAt_logDerivPrincipalParts (f : ℂ → ℂ) (s : Finset ℂ) {z : ℂ} (hz : z ∉ s) :
    AnalyticAt ℂ (logDerivPrincipalParts f s) z := by
  unfold logDerivPrincipalParts
  apply Finset.analyticAt_fun_sum s
  intro a ha
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (by rintro rfl; exact hz ha))

/-- The logarithmic-derivative remainder is meromorphic before its removable values are filled. -/
theorem meromorphicOn_logDeriv_remainder {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (s : Finset ℂ) :
    MeromorphicOn (fun z => logDeriv f z - logDerivPrincipalParts f s z) K := by
  intro z hz
  apply (hf z hz).meromorphicAt.logDeriv.sub
  unfold logDerivPrincipalParts
  apply MeromorphicAt.fun_sum
  intro a ha
  exact (MeromorphicAt.const _ _).div ((analyticAt_id.sub analyticAt_const).meromorphicAt)

/-- Removing all finite-order zeros gives an analytic normal form on the entire set. -/
theorem analyticOnNhd_logDeriv_remainder {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    (hfinite : ∀ z ∈ K, analyticOrderAt f z ≠ ⊤) (s : Finset ℂ)
    (hcover : ∀ z ∈ K, f z = 0 → z ∈ s) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (fun z => logDeriv f z - logDerivPrincipalParts f s z) K) K := by
  intro c hc
  have hmer := meromorphicOn_logDeriv_remainder hf s
  by_cases hcs : c ∈ s
  · obtain ⟨g,hg,he⟩ := exists_analytic_logDeriv_remainder (hf c hc) (hfinite c hc)
    have hs : AnalyticAt ℂ (logDerivPrincipalParts f (s.erase c)) c :=
      analyticAt_logDerivPrincipalParts f (s.erase c) (Finset.notMem_erase _ _)
    apply analyticAt_normalForm_of_punctured_eq hmer hc (hg.sub hs)
    filter_upwards [he] with z hz
    have hsplit : logDerivPrincipalParts f s z =
        (analyticOrderNatAt f c : ℂ)/(z-c) + logDerivPrincipalParts f (s.erase c) z := by
      exact (Finset.add_sum_erase s (fun a => (analyticOrderNatAt f a : ℂ)/(z-a)) hcs).symm
    rw [hz, hsplit]
    simp only [Pi.sub_apply]
    ring
  · have hfc : f c ≠ 0 := fun hz => hcs (hcover c hc hz)
    have ha := (analyticAt_logDeriv (hf c hc) hfc).sub (analyticAt_logDerivPrincipalParts f s hcs)
    exact analyticAt_normalForm_of_punctured_eq hmer hc ha (Filter.EventuallyEq.refl _ _)

/-- At a nonzero point outside the listed poles the filled remainder has its original value. -/
theorem logDeriv_remainder_normalForm_eq {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    (s : Finset ℂ) {z : ℂ} (hz : z ∈ K) (hzs : z ∉ s) (hfz : f z ≠ 0) :
    toMeromorphicNFOn (fun z => logDeriv f z - logDerivPrincipalParts f s z) K z =
      logDeriv f z - logDerivPrincipalParts f s z := by
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (meromorphicOn_logDeriv_remainder hf s) hz]
  have ha : AnalyticAt ℂ (fun z => logDeriv f z - logDerivPrincipalParts f s z) z :=
    (analyticAt_logDeriv (hf z hz) hfz).sub (analyticAt_logDerivPrincipalParts f s hzs)
  exact congrFun (toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt) z

end NLS.ComplexAnalysis
