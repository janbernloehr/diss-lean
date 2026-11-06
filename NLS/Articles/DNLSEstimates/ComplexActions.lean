import NLS.Articles.DNLSEstimates.HigherActions
import NLS.ZakharovShabat.SourceSection28Original
import NLS.ZakharovShabat.Section28ComplexChiRatio

/-!
# Complex action and gap estimates in Section 6

One L²-open neighborhood is chosen before all weights and indices. The
corrected constants are 2048 for chi and 4608 for the original action.
The rational intermediate bound is replaced by a positive expression
valid also at the boundary cutoff. No real-source restriction replaces
the paper's complex source domain.
-/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

variable {W₀ W V Wa B U T S : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- Lemma 17's final bound with corrected constant, on the actual closed
complex gap and in the exact physical H¹ norm. -/
theorem lemma_seventeen (Q : SourceSection28Data D A B U T S)
    (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ S)
    (n : ℤ) (hn : 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ 1+|(n : ℝ)|)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num)
      (sobolevSourceInclusion a) n) :
    ‖sourceActionChi (by simp) (by norm_num) n (sobolevSourceInclusion a) z‖ ≤
      2048*(1+‖sourcePhysicalH1Coordinates a‖^2) :=
  (Q.physical_H1_bounds a ha).1 n hn z hz

/-- Proposition 18 on complex H¹ sources, retaining the original actions,
the printed threshold and the gap-squared factor; constant 4608 is used. -/
theorem proposition_eighteen (Q : SourceSection28Data D A B U T S)
    (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ S)
    (n : ℤ) (hn : 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ |(n : ℝ)|) :
    ‖sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a)‖ ≤
      4608*(1+‖sourcePhysicalH1Coordinates a‖^2)*
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
          (sobolevSourceInclusion a) n‖^2 :=
  (Q.physical_H1_bounds a ha).2 n hn

/-- The common complex domain and all preceding original family data are
constructed before choosing any source, weight or index. -/
theorem complex_action_domain :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2),
      ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U T S : Set (CoeffPair 2), SourceSection28Data D A B U T S :=
  sourceSection28_original

/-- A corrected rational intermediate estimate in Lemma 17. Its denominator
is positive at |n|=N, and it covers both signed spectral directions. -/
theorem lemma_seventeen_ratio (X : Set (CoeffPair 2)) (hX : IsOpen X)
    (hrX : realTypeSourceLocus 2 ⊆ X) :
    ∃ O : Set (CoeffPair 2), IsOpen O ∧ IsConnected O ∧ realTypeSourceLocus 2 ⊆ O ∧
      O ⊆ X ∧ ∀ a ∈ O,
        ∀ φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2,
          weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential a →
          ∀ N : ℕ, 8*‖φ‖^2 ≤ 1+(N : ℝ) → ∀ n : ℤ, N ≤ n.natAbs →
            ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) a n,
              ‖sourceActionChi (by simp) (by norm_num) n a z‖ ≤
                128*((|(n : ℝ)|+N+2/5)/(|(n : ℝ)|-N+3/10)) :=
  section28_complex_chi_ratio_neighborhood X hX hrX

/-- Formula (16) uses the actual analytically filled action/gap quotient,
so it is meaningful at collapsed gaps as well as noncollapsed ones. -/
theorem normalized_action_bound (Q : SourceSection28Data D A B U T S)
    (a : CoeffPair 2) (ha : a ∈ S) (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) a n,
      ‖sourceActionChi (by simp) (by norm_num) n a z‖ ≤ K) :
    ‖4*sourceNormalizedIndexedAction (by simp) (by norm_num) n a‖ ≤ 9*K :=
  Q.normalized_bound a ha n K hK hb

/-- Formula (15): the filled quotient differs from one by an actual ℓ²
sequence, with a locally uniform ℓ² norm on the complex domain. -/
theorem normalized_action_locally_uniform (Q : SourceSection28Data D A B U T S)
    (a : CoeffPair 2) (ha : a ∈ S) :
    ∃ O : Set (CoeffPair 2), IsOpen O ∧ a ∈ O ∧ O ⊆ S ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ O, ∃ c : Coeff 2,
        (∀ n : ℤ, c n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n b-1) ∧
        ‖c‖ ≤ C :=
  Q.normalized_locally_uniform a ha

/-- The uniform-on-H¹-balls consequence following formula (15). -/
theorem normalized_action_H1_ball (Q : SourceSection28Data D A B U T S) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeSobolevSourceLocus,
      ‖sourcePhysicalH1Coordinates a.val‖ ≤ R → ∃ c : Coeff 2,
        (∀ n : ℤ, c n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n
          (sobolevSourceInclusion a.val)-1) ∧ ‖c‖ ≤ C :=
  Q.normalized_uniform_H1_ball R

/-- The continuity and convergence assertion in the proof of Theorem 3
holds throughout the weighted part of the chosen L² neighborhood. -/
theorem weighted_action_continuous (Q : SourceSection28Data D A B U T S)
    (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ContinuousOn (fun a : CoeffPair 2 => ∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖)
      (normalizedWeightedSource w ⁻¹' S) ∧
    ∀ a : CoeffPair 2, normalizedWeightedSource w a ∈ S →
      Summable (fun n : ℤ => (w (2*n))^2*
        ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) :=
  ⟨Q.weighted_continuous w hw,fun a ha => Q.weighted_summable w hw a ha⟩

end NLS.Articles.DNLSEstimates
