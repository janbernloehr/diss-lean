import NLS.SequenceSpaces.CoefficientCompactness
import NLS.SequenceSpaces.Weighted

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal

namespace NLS.WeightedCoeff



/-- Bounded weighted coefficient sequences have a subsequence converging in
every original raw Fourier coordinate, with limit in the same weighted space. -/
theorem exists_coefficientwise_tendsto_subseq_of_bounded
    (w : Weight) {p : ℝ≥0∞} [Fact (1≤p)] (a : ℕ → WeightedCoeff w p)
    (hb : Bornology.IsBounded (range a)) :
    ∃ b : WeightedCoeff w p, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℤ, Tendsto (fun k => (a (σ k)).val n) atTop (𝓝 (b.val n)) := by
  let T := weightIsometry w p
  have hb' : Bornology.IsBounded (range (fun k => T (a k))) := by
    obtain ⟨B,hB⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B,?_⟩
    rintro _ ⟨k,rfl⟩
    simpa only [LinearIsometryEquiv.norm_map] using hB _ ⟨k,rfl⟩
  obtain ⟨b,σ,hσ,ht⟩ := Coeff.exists_coefficientwise_tendsto_subseq_of_bounded (fun k => T (a k)) hb'
  refine ⟨T.symm b,σ,hσ,?_⟩
  intro n
  have h := (ht n).div_const (w n : ℂ)
  change Tendsto (fun k => ((w n : ℂ)*(a (σ k)).val n)/(w n : ℂ)) atTop
    (𝓝 ((b n)/(w n : ℂ))) at h
  have hval : (T.symm b).val n=b n/(w n : ℂ) := by
    apply (eq_div_iff (w.complex_ne_zero n)).mpr
    have he := congrArg (fun v : Coeff p => v n) (T.apply_symm_apply b)
    change (w n : ℂ)*(T.symm b).val n=b n at he
    simpa only [mul_comm] using he
  rw [hval]
  simpa only [mul_div_cancel_left₀ _ (w.complex_ne_zero n)] using h

/-- At the weighted Hilbert exponent, raw coefficient convergence and
convergence of the original weighted norms imply strong convergence. -/
theorem tendsto_of_coefficientwise_of_norm_sq
    (w : Weight) {α : Type*} {l : Filter α} (a : α → WeightedCoeff w 2) (b : WeightedCoeff w 2)
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val n) l (𝓝 (b.val n)))
    (hn : Tendsto (fun k => ‖a k‖^2) l (𝓝 (‖b‖^2))) :
    Tendsto a l (𝓝 b) := by
  let T := weightIsometry w 2
  have ht' (n : ℤ) : Tendsto (fun k => T (a k) n) l (𝓝 (T b n)) :=
    (ht n).const_mul (w n : ℂ)
  have hn' : Tendsto (fun k => ‖T (a k)‖^2) l (𝓝 (‖T b‖^2)) := by
    simpa only [LinearIsometryEquiv.norm_map] using hn
  have h := T.symm.continuous.continuousAt.tendsto.comp
    (Coeff.tendsto_of_coefficientwise_of_norm_sq (fun k => T (a k)) (T b) ht' hn')
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using h

end NLS.WeightedCoeff
