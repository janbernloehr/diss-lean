import NLS.SequenceSpaces.LocalTailActionFactor

/-! # Analytic tail-action quotients at arbitrary basepoints

The finite head stays linear. Sign invariance and stationarity on an
open domain give a sequence-valued factor near any of its points.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Local descent through the tail sum, for an already descended lift. -/
theorem exists_local_tail_sum_factor_of_chart_at (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (G : (Coeff q × Coeff q) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (z₀ : Coeff p × Coeff p) (hbase : z₀ ∈ V)
    (L : TailSumChart S (pairMixedSquare S '' V) (pairMixedSquare (p := p) (q := q) S z₀))
    (hG : AnalyticOnNhd ℂ G (pairMixedSquare S '' V))
    (he : ∀ z ∈ V, G (pairMixedSquare S z) = f z)
    (hsplit : ∀ b ∈ pairMixedSquare S '' V, ∀ k ∉ S,
      fderiv ℂ G b (actionSplitDirection q k) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → F,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧
      (fun z => tailSumCLM S (pairMixedSquare S z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      ∀ z ∈ Z, g (tailSumCLM S (pairMixedSquare S z)) = f z := by
  let Q := pairMixedSquare (p := p) (q := q) S
  have hopen : IsOpen (Q '' V) := isOpenMap_pairMixedSquare hp S V hV
  have hQ : Continuous Q := continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn
  obtain ⟨Z,hZ,h0Z,hZV,himage,hrec⟩ := NLS.ComplexAnalysis.exists_local_factor_lift
    Q (tailSumCLM S) f G (L.factor G) V L.source L.target z₀ hQ hV L.source_open
    hbase L.base_mem L.source_subset L.image_source he
    (L.factor_apply (doublingExponent_ne_top hp) hopen G hG.differentiableOn hsplit)
  exact ⟨Z,L.target,L.factor G,hZ,h0Z,hZV,L.target_open,himage,L.analyticOnNhd_factor G hG,hrec⟩


theorem exists_local_tail_sum_factor_of_recovery_at (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (G : (Coeff q × Coeff q) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (z₀ : Coeff p × Coeff p) (hbase : z₀ ∈ V)
    (hG : AnalyticOnNhd ℂ G (pairMixedSquare S '' V))
    (he : ∀ z ∈ V, G (pairMixedSquare S z) = f z)
    (hsplit : ∀ b ∈ pairMixedSquare S '' V, ∀ k ∉ S,
      fderiv ℂ G b (actionSplitDirection q k) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → F,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧
      (fun z => tailSumCLM S (pairMixedSquare S z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      ∀ z ∈ Z, g (tailSumCLM S (pairMixedSquare S z)) = f z := by
  obtain ⟨L⟩ := exists_tailSumChart S (pairMixedSquare (q := q) S '' V)
    (isOpenMap_pairMixedSquare hp S V hV) (pairMixedSquare (p := p) (q := q) S z₀) ⟨z₀,hbase,rfl⟩
  exact exists_local_tail_sum_factor_of_chart_at hp S f G V hV z₀ hbase L hG he hsplit

/-- Sign symmetry and tail stationarity give a local factor while
retaining the finite head linearly. -/
theorem exists_local_tail_action_factor_of_sign_invariance_at (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r)
    (V : Set (Coeff p × Coeff p)) (hV : IsOpen V) (z₀ : Coeff p × Coeff p) (hbase : z₀ ∈ V)
    (hf : AnalyticOnNhd ℂ f V)
    (hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (hrot : ∀ z ∈ V, ∀ k ∉ S,
      fderiv ℂ f z (actionRotationVectorCLM p k z) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → Coeff r,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧
      (fun z => tailSumCLM S (pairMixedSquare S z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      ∀ z ∈ Z, g (tailSumCLM S (pairMixedSquare S z)) = f z := by
  let Q := pairMixedSquare (p := p) (q := q) S
  let G := tailSquareDescent (q := q) S f V
  have hG : AnalyticOnNhd ℂ G (Q '' V) :=
    analyticOnNhd_tailSquareDescent hp S f V hV hf hsign
  have he (z : Coeff p × Coeff p) (hz : z ∈ V) : G (Q z) = f z :=
    tailSquareDescent_apply S f V hsign z hz
  have hsplit := fderiv_actionSplit_eq_zero_of_tail_stationarity hp S f G V hV
    hf.differentiableOn hG he hrot
  exact exists_local_tail_sum_factor_of_recovery_at hp S f G V hV z₀ hbase hG he hsplit


end NLS.Coeff
