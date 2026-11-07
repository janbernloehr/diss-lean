import NLS.ZakharovShabat.SourceGapCompactGain
import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.SequenceSpaces.SobolevEvenSampling
import NLS.SequenceSpaces.SobolevFamilyCompactness

/-!
# A compact Sobolev gain in the exact original source coordinates

A common actual-gap majorant supplies a uniformly bounded positive gain.
Any strictly smaller gain then gives a continuous exact source realization.
Compactness is retained for the next iteration without assuming continuity
of the stronger bounded realization.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact source family and a continuous realization at order t gain
compact regularity at t+σ from a common gap majorant at t+s, where σ<s
and s obeys the exact algebraic remainder threshold. -/
theorem exists_compact_source_sobolev_step
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (φ : T → realTypeSourceSubmodule p) (hφ : Continuous φ)
    (t s σ : ℝ) (ht : 0 ≤ t) (hs : 0 < s) (hσs : σ < s)
    (hsp : s*p.toReal < min 1 (p.toReal-1))
    (A : T → CoeffPair p) (hA : Continuous A)
    (hAc : ∀ x n, (A x).fst n = (Weight.sobolev t n:ℂ)*(φ x).val.fst n ∧
      (A x).snd n = (Weight.sobolev t n:ℂ)*(φ x).val.snd n)
    (Γ : Coeff p)
    (hΓ : Memℓp (fun n : ℤ => (Weight.sobolev (t+s) n:ℂ)*Γ n) p)
    (hgap : ∀ x n, ‖sourcePeriodicGapDisplacement hp hp1 (φ x).val n‖ ≤ ‖Γ n‖) :
    ∃ B : T → CoeffPair p, Continuous B ∧
      (∀ x n, (B x).fst n = (Weight.sobolev (t+σ) n:ℂ)*(φ x).val.fst n ∧
        (B x).snd n = (Weight.sobolev (t+σ) n:ℂ)*(φ x).val.snd n) ∧
      IsCompact (range B) := by
  let w := sourceSobolevSpectralWeight t ht
  let ψ := fun x => normalizedWeightedPeriodOne w (A x)
  have hψ : Continuous ψ := (normalizedWeightedPeriodOne w).continuous.comp hA
  have hrel : ∀ x, w.forgetPairWeight (ψ x) = sourceWeightedPeriodOne (φ x).val := by
    intro x
    have he : normalizedWeightedSource w (A x) = (φ x).val := by
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext n
      · change (normalizedWeightedSource w (A x)).fst n = (φ x).val.fst n
        rw [normalizedWeightedSource_fst,(hAc x n).1]
        rw [show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n]
        exact mul_div_cancel_left₀ _ ((Weight.sobolev t).complex_ne_zero n)
      · change (normalizedWeightedSource w (A x)).snd n = (φ x).val.snd n
        rw [normalizedWeightedSource_snd,(hAc x n).2]
        rw [show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n]
        exact mul_div_cancel_left₀ _ ((Weight.sobolev t).complex_ne_zero n)
    exact (forget_normalizedWeightedPeriodOne w (A x)).trans (congrArg sourceWeightedPeriodOne he)
  have hΓt : Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*Γ n) p := by
    apply hΓ.mono'
    intro n
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev t).positive n),abs_of_pos ((Weight.sobolev (t+s)).positive n)]
    exact mul_le_mul_of_nonneg_right (Weight.sobolev_mono (by linarith only [hs] : t ≤ t+s) n)
      (norm_nonneg _)
  let Γt : Coeff p := ⟨_,hΓt⟩
  have hΓs : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*Γt n) p := by
    change Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*((Weight.sobolev t n:ℂ)*Γ n)) p
    simpa only [Weight.sobolev_add,Complex.ofReal_mul,mul_assoc,mul_left_comm,mul_comm] using hΓ
  have hdom : ∀ x n, ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 (φ x).val n‖ ≤ ‖Γt n‖ := by
    intro x n
    change ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 (φ x).val n‖ ≤
      ‖(Weight.sobolev t n:ℂ)*Γ n‖
    rw [show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n]
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev t).positive n)] using
      mul_le_mul_of_nonneg_left (hgap x n) ((Weight.sobolev t).positive n).le
  obtain ⟨F,hF,C,hC,hbound⟩ := exists_uniform_sobolev_gain_on_compact_source_family
    hp hp1 w φ ψ hφ hψ hrel s hs hsp Γt hΓs hdom
  have hsample₁ (x : T) := Coeff.exists_sobolev_even_sample_le (F x).fst
    (fun n => (φ x).val.fst n) t s hs.le (by
      intro n
      rw [(hF x (2*n)).1]
      congr 1
      have he := congrArg (fun b : WeightedCoeffPair SpectralWeight.one.toWeight p => b.fst.val (2*n)) (hrel x)
      have he' : (ψ x).fst.val (2*n) = (φ x).val.fst n := by simpa using he
      rw [he',show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n])
  have hsample₂ (x : T) := Coeff.exists_sobolev_even_sample_le (F x).snd
    (fun n => (φ x).val.snd n) t s hs.le (by
      intro n
      rw [(hF x (2*n)).2]
      congr 1
      have he := congrArg (fun b : WeightedCoeffPair SpectralWeight.one.toWeight p => b.snd.val (2*n)) (hrel x)
      have he' : (ψ x).snd.val (2*n) = (φ x).val.snd n := by simpa using he
      rw [he',show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n])
  choose F₁ hF₁ hB₁ using hsample₁
  choose F₂ hF₂ hB₂ using hsample₂
  have hcf := (CoeffPair.toMax p).continuous.comp (continuous_subtype_val.comp hφ)
  have hc₁ (n : ℤ) : Continuous (fun x => (φ x).val.fst n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp (continuous_fst.comp hcf)
  have hc₂ (n : ℤ) : Continuous (fun x => (φ x).val.snd n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp (continuous_snd.comp hcf)
  obtain ⟨G₁,hG₁,he₁⟩ := Coeff.exists_continuous_lower_sobolev_family
    (fun x n => (φ x).val.fst n) hc₁ (t+s) (t+σ) (by linarith only [hσs]) F₁ hF₁ C hC
    (fun x => (hB₁ x).trans ((WithLp.norm_fst_le (Coeff p) (F x)).trans (hbound x)))
  obtain ⟨G₂,hG₂,he₂⟩ := Coeff.exists_continuous_lower_sobolev_family
    (fun x n => (φ x).val.snd n) hc₂ (t+s) (t+σ) (by linarith only [hσs]) F₂ hF₂ C hC
    (fun x => (hB₂ x).trans ((WithLp.norm_snd_le (Coeff p) (F x)).trans (hbound x)))
  let B := fun x => CoeffPair.inlCLM (G₁ x)+CoeffPair.inrCLM (G₂ x)
  have hB : Continuous B :=
    ((CoeffPair.inlCLM (p := p)).continuous.comp hG₁).add
      ((CoeffPair.inrCLM (p := p)).continuous.comp hG₂)
  refine ⟨B,hB,?_,isCompact_range hB⟩
  intro x n
  constructor
  · change G₁ x n+0 = _
    rw [add_zero,he₁]
  · change 0+G₂ x n = _
    rw [zero_add,he₂]

end NLS.ZakharovShabat
