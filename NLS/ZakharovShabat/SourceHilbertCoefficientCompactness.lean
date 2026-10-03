import NLS.SequenceSpaces.CoefficientCompactness
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.SequenceSpaces.Reflection

/-! # Coefficient compactness of bounded real sources

The second component is fixed by the first through the real-type relation.
For Hilbert sources, coefficient convergence plus convergence of the source
energy therefore gives strong convergence in the original pair norm.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- The real-type condition determines the entire second coefficient sequence. -/
theorem realTypeSource_snd_eq_star_reflection_fst
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : realTypeSourceSubmodule p) :
    φ.val.snd = star (Coeff.reflection φ.val.fst) := by
  ext n
  exact φ.property n

/-- A real Hilbert pair has twice the energy of its first component. -/
theorem realTypeSource_norm_sq_eq_two_mul_fst (φ : realTypeSourceSubmodule 2) :
    ‖φ‖^2 = 2 * ‖φ.val.fst‖^2 := by
  change ‖φ.val‖^2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, realTypeSource_snd_eq_star_reflection_fst,
    norm_star, Coeff.reflection.norm_map]
  ring

/-- Bounded real sources have a subsequence converging at every Fourier
coefficient to a source in the same real sequence space. -/
theorem exists_realTypeSource_coefficientwise_subseq
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : ℕ → realTypeSourceSubmodule p)
    (hb : Bornology.IsBounded (range a)) :
    ∃ b : realTypeSourceSubmodule p, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ n : ℤ, Tendsto (fun k => (a (σ k)).val.fst n) atTop (𝓝 (b.val.fst n))) ∧
      (∀ n : ℤ, Tendsto (fun k => (a (σ k)).val.snd n) atTop (𝓝 (b.val.snd n))) := by
  have hf : Bornology.IsBounded (range (fun k => (a k).val.fst)) := by
    obtain ⟨B, hB⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (WithLp.norm_fst_le _ (a k).val).trans (hB _ ⟨k, rfl⟩)
  obtain ⟨b, σ, hσ, ht⟩ := Coeff.exists_coefficientwise_tendsto_subseq_of_bounded
    (fun k => (a k).val.fst) hf
  let ψ : realTypeSourceSubmodule p :=
    ⟨(CoeffPair.toMax p).symm (b, star (Coeff.reflection b)), fun _ => rfl⟩
  refine ⟨ψ, σ, hσ, ht, ?_⟩
  intro n
  simpa only [show ∀ k, (a (σ k)).val.snd n = conj ((a (σ k)).val.fst (-n)) from
    fun k => (a (σ k)).property n] using!
    Complex.continuous_conj.continuousAt.tendsto.comp (ht (-n))

/-- In the real Hilbert source space, no energy loss at a coefficientwise
limit is exactly the condition needed to upgrade to strong convergence. -/
theorem tendsto_realTypeSource_of_coefficientwise_of_norm_sq
    {α : Type*} {l : Filter α} (a : α → realTypeSourceSubmodule 2)
    (b : realTypeSourceSubmodule 2)
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val.fst n) l (𝓝 (b.val.fst n)))
    (hn : Tendsto (fun k => ‖a k‖^2) l (𝓝 (‖b‖^2))) :
    Tendsto a l (𝓝 b) := by
  have he (φ : realTypeSourceSubmodule 2) : ‖φ.val.fst‖^2 = ‖φ‖^2/2 := by
    rw [realTypeSource_norm_sq_eq_two_mul_fst]
    ring
  have hnf : Tendsto (fun k => ‖(a k).val.fst‖^2) l (𝓝 (‖b.val.fst‖^2)) := by
    simp_rw [he]
    exact hn.div_const 2
  have hf := Coeff.tendsto_of_coefficientwise_of_norm_sq (fun k => (a k).val.fst) b.val.fst ht hnf
  have hs : Tendsto (fun k => (a k).val.snd) l (𝓝 b.val.snd) := by
    simp_rw [realTypeSource_snd_eq_star_reflection_fst]
    exact (Coeff.reflection.continuous.continuousAt.tendsto.comp hf).star
  apply tendsto_subtype_rng.mpr
  exact (CoeffPair.toMax 2).symm.continuous.continuousAt.tendsto.comp (hf.prodMk_nhds hs)

end NLS.ZakharovShabat
