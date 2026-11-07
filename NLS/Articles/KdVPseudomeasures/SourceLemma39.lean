import NLS.Articles.KdVPseudomeasures.SourceUniformEndpointFrequencyDecay
import NLS.Articles.KdVPseudomeasures.SourceEndpointActionDecay

/-! Full Lemma 3.9 for the genuine KdV frequencies and original
canonical actions, uniformly on every original physical endpoint norm ball. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- The literal action-corrected uniform o(1) remainder. The same
cutoff serves the complete original norm ball and every later mode. -/
theorem sourceLemma3_9 (r : ℝ) (hr : AdmissiblePredualOrder r) (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        ‖(hillRoughKdVFrequency n (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℂ)-
            ((2*(Real.pi:ℂ)*(n:ℤ))^3-6*originalCanonicalHillAction n (sourceOriginalPotential r hr q))‖ < ε := by
  obtain ⟨Nr,hNr⟩ := source_uniform_endpoint_frequency_remainder r hr R (ε/2) (by positivity)
  obtain ⟨Na,hNa⟩ := source_uniform_endpoint_action_decay r hr R (ε/12) (by positivity)
  refine ⟨max 1 (max Nr Na),le_max_left _ _,?_⟩
  intro q hq n hn
  have hnr : Nr ≤ (n:ℕ) := (le_max_left Nr Na).trans ((le_max_right 1 _).trans hn)
  have hna : Na ≤ (n:ℕ) := (le_max_right Nr Na).trans ((le_max_right 1 _).trans hn)
  have hR := hNr q hq n hnr
  have hA := hNa q hq n hna
  have he :
      (hillRoughKdVFrequency n (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℂ)-
          ((2*(Real.pi:ℂ)*(n:ℤ))^3-6*originalCanonicalHillAction n (sourceOriginalPotential r hr q)) =
        ((hillRoughKdVFrequency n (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℂ)-
          (2*(Real.pi:ℂ)*(n:ℤ))^3)+6*originalCanonicalHillAction n (sourceOriginalPotential r hr q) := by ring
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_mul,Complex.norm_ofNat]
  linarith

end NLS.Articles.KdVPseudomeasures
