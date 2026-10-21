import NLS.ZakharovShabat.SourceSection20Frequencies

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The original scalar moment sequence is bounded throughout the unchanged
complex source domain, and its infinity realization retains every coordinate. -/
theorem sequence_top_eq_inclusion (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    A.frequencySequence ⊤ ψ =
      Coeff.exponentInclusion (show p ≤ ⊤ from le_top) (A.frequencySequence p ψ) := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    calc
      _ ≤ ENNReal.ofReal p.toReal := ENNReal.ofReal_le_ofReal
        (by linarith [ENNReal.toReal_nonneg (a := p)])
      _ = p := ENNReal.ofReal_toReal hp
  have he := (Q.sequence p hp hp1 hhalf).1 ψ hψ
  have hmem : Memℓp (fun n => A.renormalizedFrequency n ψ) ⊤ := by
    have hf : (fun n => A.renormalizedFrequency n ψ) = ⇑(A.frequencySequence p ψ) :=
      funext (fun n => (he n).symm)
    rw [hf]
    exact (lp.memℓp _).of_exponent_ge le_top
  ext n
  exact (Coeff.ofFunctionOrZero_apply_of_mem ⊤ _ hmem n).trans (he n).symm

/-- Theorem 20.5 also has the infinity target on the same original U,
with the actual scalar frequencies and both complex and real analyticity. -/
theorem sequence_analytic_top :
    (∀ ψ ∈ U, ∀ n, A.frequencySequence ⊤ ψ n = A.renormalizedFrequency n ψ) ∧
    AnalyticOnNhd ℂ (A.frequencySequence ⊤) U ∧
    AnalyticOnNhd ℝ (A.frequencySequence ⊤) U ∧
    ∀ φ : realTypeSourceSubmodule p, ∀ n, (A.frequencySequence ⊤ φ.val n).im = 0 := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    calc
      _ ≤ ENNReal.ofReal p.toReal := ENNReal.ofReal_le_ofReal
        (by linarith [ENNReal.toReal_nonneg (a := p)])
      _ = p := ENNReal.ofReal_toReal hp
  obtain ⟨he,ha,hR,hr⟩ := Q.sequence_analytic p hp hp1 hhalf
  let L := Coeff.exponentInclusion (show p ≤ ⊤ from le_top)
  have hA : AnalyticOnNhd ℂ (A.frequencySequence ⊤) U := by
    apply AnalyticOnNhd.congr Q.source_open
      (show AnalyticOnNhd ℂ (fun ψ => L (A.frequencySequence p ψ)) U from
        fun ψ hψ => (L.analyticAt _).comp (ha ψ hψ))
    exact fun ψ hψ => (Q.sequence_top_eq_inclusion ψ hψ).symm
  refine ⟨?_,hA,hA.restrictScalars,?_⟩
  · intro ψ hψ n
    rw [Q.sequence_top_eq_inclusion ψ hψ]
    exact he ψ hψ n
  · intro φ n
    rw [Q.sequence_top_eq_inclusion φ.val (Q.real_subset φ.property)]
    exact hr φ n

/-- Every allowed target exponent, including infinity, uses the same
literal frequency sequence and unchanged complex source domain. -/
theorem sequence_analytic_all (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    (∀ ψ ∈ U, ∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
    AnalyticOnNhd ℂ (A.frequencySequence r) U ∧ AnalyticOnNhd ℝ (A.frequencySequence r) U ∧
    ∀ φ : realTypeSourceSubmodule p, ∀ n, (A.frequencySequence r φ.val n).im = 0 := by
  by_cases hr : r = ⊤
  · subst r
    exact Q.sequence_analytic_top
  · exact Q.sequence_analytic r hr hr1 hpr

/-- The literal scalar frequency belongs to every allowed target, with no
fallback in the sequence constructor on the original source domain. -/
theorem frequency_memℓp_all (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    Memℓp (fun n => A.renormalizedFrequency n ψ) r := by
  have he := (Q.sequence_analytic_all r hr1 hpr).1 ψ hψ
  have hf : (fun n => A.renormalizedFrequency n ψ) = ⇑(A.frequencySequence r ψ) :=
    funext (fun n => (he n).symm)
  rw [hf]
  exact lp.memℓp _

/-- At zero the same frequency realization is zero for all allowed targets. -/
theorem sequence_zero_all (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) : A.frequencySequence r 0 = 0 := by
  ext n
  rw [(Q.sequence_analytic_all r hr1 hpr).1 0 (Q.real_subset (by simp [realTypeSourceLocus])) n]
  exact A.renormalizedFrequency_eq_zero_at_zero n

end NLS.ZakharovShabat.SourceSection20Data
