import NLS.ZakharovShabat.SourceSecondMomentActionOrigin
import NLS.ZakharovShabat.SourceHilbertGapOpening
import NLS.ZakharovShabat.SourceFrequencyOrigin

/-! # The frequency slope on a single action opened from zero -/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B X : Set (CoeffPair 2)}
  {t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Opening one Birkhoff coordinate from zero gives exactly one nonzero
action, with value one half of the squared real amplitude. -/
theorem hilbertGapOpening_zero_source_action
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (k n : ℤ) (a : ℝ) :
    sourceComplexAction (by simp) (by norm_num) n (D.hilbertGapOpening 0 k a).val =
      if n = k then ((a^2/2 : ℝ) : ℂ) else 0 := by
  have hfree (j : ℤ) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (0 : CoeffPair 2)) (periodOnePotential_mem 0) j = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero (p := 2) (by simp) (by norm_num) j
  rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n _
    (D.hilbertGapOpening 0 k a).property]
  by_cases hnk : n = k
  · subst n
    rw [if_pos rfl]
    apply Complex.ext
    · simpa only [ofReal_re] using D.hilbertGapOpening_action_same_of_closed 0 k (hfree k) a
    · simpa only [ofReal_im] using
        (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) _
          (D.hilbertGapOpening 0 k a).property k).2.1
  · rw [if_neg hnk]
    apply (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) _
      (D.hilbertGapOpening 0 k a).property n).2.2.mpr
    rw [sourcePeriodicGapDisplacement_apply]
    exact (D.hilbertGapOpening_gap_zero_iff_of_ne 0 k n hnk a).mpr (hfree n)

end SourceBirkhoffMapComplexData
namespace SourceAbelianMomentAtlas
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {W₀ B X : Set (CoeffPair 2)} {t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual frequency divided by the opened action tends to minus
twice the Kronecker delta. Both signs of the opening amplitude are allowed. -/
theorem tendsto_frequency_div_opening_action
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2 ⊆ V)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t) (n k : ℤ) :
    Tendsto (fun a : ℝ => A.renormalizedFrequency n (D.hilbertGapOpening 0 k a).val /
      ((a^2/2 : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 (if k = n then (-2 : ℂ) else 0)) := by
  obtain ⟨f,hf,hfzero,hfactor⟩ := A.exists_singleAction_frequency_factor_at_zero hs hV hrealV n k
  let γ := fun a : ℝ => (D.hilbertGapOpening 0 k a).val
  have hγ : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (0 : CoeffPair 2)) := by
    have he := ((realTypeSourceSubmodule 2).subtypeL.continuous.comp
      (D.continuous_hilbertGapOpening 0 k)).tendsto 0
    change Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (D.hilbertGapOpening 0 k 0).val) at he
    rw [D.hilbertGapOpening_zero] at he
    exact he
  have hl := (hf.tendsto.comp hγ).mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  rw [hfzero] at hl
  apply hl.congr'
  filter_upwards [hγ.eventually hfactor |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with a ha hane
  have hsupp (j : ℤ) (hjk : j ≠ k) : sourceComplexAction (by simp) (by norm_num) j (γ a) = 0 := by
    simp only [γ,D.hilbertGapOpening_zero_source_action,if_neg hjk]
  have he := ha (D.hilbertGapOpening 0 k a).property hsupp
  have hact := D.hilbertGapOpening_zero_source_action k k a
  simp at hact
  dsimp only [γ] at he ⊢
  rw [he,hact]
  have hane' : a ≠ 0 := hane
  have hn : ((a^2/2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast div_ne_zero (pow_ne_zero 2 hane') (by norm_num : (2 : ℝ) ≠ 0)
  field_simp
  push_cast
  dsimp only [Function.comp_def]
  ring

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
