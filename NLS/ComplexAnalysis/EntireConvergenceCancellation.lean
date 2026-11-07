import NLS.ComplexAnalysis.EntireLimit
import Mathlib.Analysis.Normed.Field.Lemmas

/-! Cancellation of a fixed entire factor in locally uniform limits.
Its countable zero set is filled by entire convergence, so cancellation
is valid there as well as at ordinary quotient points. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem const_product_scalar_unique {X : Type*} (F : ℕ → X → ℂ) (P : X → ℂ)
    (hne : P ≠ 0) (A B : ℂ)
    (hA : ∀ x, Tendsto (fun N => A*F N x) atTop (𝓝 (P x)))
    (hB : ∀ x, Tendsto (fun N => B*F N x) atTop (𝓝 (P x))) : A = B := by
  obtain ⟨x,hx⟩ : ∃ x, P x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hleft := (hA x).const_mul B
  have hright := (hB x).const_mul A
  have hseq : (fun N => B*(A*F N x)) = (fun N => A*(B*F N x)) := by
    funext N
    ring
  rw [hseq] at hleft
  exact (mul_right_cancel₀ hx (tendsto_nhds_unique hleft hright)).symm

theorem tendstoLocallyUniformlyOn_const_family {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (S : Set X) : TendstoLocallyUniformlyOn (fun _ : ℕ => f) f atTop S := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Eventually.of_forall (fun _ z _ => by simpa only [dist_self] using hε)

theorem tendstoLocallyUniformlyOn_univ_of_countable_exceptional
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ n, Differentiable ℂ (F n)) (hf : AnalyticOnNhd ℂ f univ)
    (S : Set ℂ) (hS : S.Countable)
    (hlim : TendstoLocallyUniformlyOn F f atTop Sᶜ) :
    TendstoLocallyUniformlyOn F f atTop univ := by
  have hL := tendstoLocallyUniformlyOn_entireSequenceLimit F hF S hS f hlim
  have hA := analyticOnNhd_entireSequenceLimit F hF S hS f hlim
  have he : entireSequenceLimit F = f :=
    (continuousOn_univ.mp hA.continuousOn).ext_on (hS.dense_compl ℂ)
      (continuousOn_univ.mp hf.continuousOn) (entireSequenceLimit_eqOn F hF S hS f hlim)
  rwa [he] at hL

theorem tendstoLocallyUniformlyOn_cancel_entire_factor
    (F G : ℕ → ℂ → ℂ) (f g p : ℂ → ℂ)
    (hG : ∀ n, Differentiable ℂ (G n)) (hg : AnalyticOnNhd ℂ g univ)
    (hp : Continuous p) (S : Set ℂ) (hS : S.Countable)
    (hnz : ∀ z ∉ S, p z ≠ 0)
    (hfactor : ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, F n z = p z*G n z)
    (hfactorLim : ∀ z : ℂ, f z = p z*g z)
    (hlim : TendstoLocallyUniformlyOn F f atTop univ) :
    TendstoLocallyUniformlyOn G g atTop univ := by
  apply tendstoLocallyUniformlyOn_univ_of_countable_exceptional G g hG hg S hS
  have hfc : Continuous f := by
    rw [show f = (fun z => p z*g z) from funext hfactorLim]
    exact hp.mul (continuousOn_univ.mp hg.continuousOn)
  have hconst := tendstoLocallyUniformlyOn_const_family p Sᶜ
  have hdiv : TendstoLocallyUniformlyOn (fun n z => F n z/p z) (fun z => f z/p z) atTop Sᶜ :=
    (hlim.mono (subset_univ _)).div₀ hconst hfc.continuousOn hp.continuousOn (fun z hz => hnz z hz)
  have hseq : ∀ᶠ n : ℕ in atTop, EqOn (fun z => F n z/p z) (G n) Sᶜ := by
    filter_upwards [hfactor] with n hn z hz
    change F n z/p z = G n z
    rw [hn z,mul_div_cancel_left₀ _ (hnz z hz)]
  have hval : EqOn (fun z => f z/p z) g Sᶜ := by
    intro z hz
    change f z/p z = g z
    rw [hfactorLim,mul_div_cancel_left₀ _ (hnz z hz)]
  exact (hdiv.congr_inseparable (hseq.mono (fun n hn z hz => Inseparable.of_eq (hn hz)))).congr_right hval

end NLS.ComplexAnalysis
