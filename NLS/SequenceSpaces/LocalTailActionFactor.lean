import NLS.SequenceSpaces.TailRotationInvariance
import NLS.SequenceSpaces.TailParameterStationarity
import NLS.SequenceSpaces.LocalTailSumDescent
import NLS.ComplexAnalysis.LocalFactorLift

/-! # Analytic tail action factors with linear head parameters

An analytic sequence-valued observable stationary under all tail rotations
has a local analytic factor through the tail quadratic radii. Both finite
head components are retained linearly, with no nonvanishing hypothesis.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [p.HolderTriple p q]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Local descent through the tail sum, for an already descended lift. -/
theorem exists_local_tail_sum_factor_of_chart (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (G : (Coeff q × Coeff q) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hbase : 0 ∈ V)
    (L : TailSumChart S (pairMixedSquare S '' V) (pairMixedSquare (p := p) (q := q) S 0))
    (hG : AnalyticOnNhd ℂ G (pairMixedSquare S '' V))
    (he : ∀ z ∈ V, G (pairMixedSquare S z) = f z)
    (hsplit : ∀ b ∈ pairMixedSquare S '' V, ∀ k ∉ S,
      fderiv ℂ G b (actionSplitDirection q k) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → F,
      IsOpen Z ∧ 0 ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧
      (fun z => tailSumCLM S (pairMixedSquare S z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      ∀ z ∈ Z, g (tailSumCLM S (pairMixedSquare S z)) = f z := by
  let Q := pairMixedSquare (p := p) (q := q) S
  have hopen : IsOpen (Q '' V) := isOpenMap_pairMixedSquare hp S V hV
  have hQ : Continuous Q := continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn
  obtain ⟨Z,hZ,h0Z,hZV,himage,hrec⟩ := NLS.ComplexAnalysis.exists_local_factor_lift
    Q (tailSumCLM S) f G (L.factor G) V L.source L.target 0 hQ hV L.source_open
    hbase L.base_mem L.source_subset L.image_source he
    (L.factor_apply (doublingExponent_ne_top hp) hopen G hG.differentiableOn hsplit)
  exact ⟨Z,L.target,L.factor G,hZ,h0Z,hZV,L.target_open,himage,L.analyticOnNhd_factor G hG,hrec⟩


theorem exists_local_tail_sum_factor_of_recovery (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (G : (Coeff q × Coeff q) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hbase : 0 ∈ V)
    (hG : AnalyticOnNhd ℂ G (pairMixedSquare S '' V))
    (he : ∀ z ∈ V, G (pairMixedSquare S z) = f z)
    (hsplit : ∀ b ∈ pairMixedSquare S '' V, ∀ k ∉ S,
      fderiv ℂ G b (actionSplitDirection q k) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → F,
      IsOpen Z ∧ 0 ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧
      (fun z => tailSumCLM S (pairMixedSquare S z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      ∀ z ∈ Z, g (tailSumCLM S (pairMixedSquare S z)) = f z := by
  obtain ⟨L⟩ := exists_tailSumChart S (pairMixedSquare (q := q) S '' V)
    (isOpenMap_pairMixedSquare hp S V hV) (pairMixedSquare (p := p) (q := q) S 0) ⟨0,hbase,rfl⟩
  exact exists_local_tail_sum_factor_of_chart hp S f G V hV hbase L hG he hsplit

/-- Sign symmetry and tail stationarity give a local factor while
retaining the finite head linearly. -/
theorem exists_local_tail_action_factor_of_sign_invariance (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r)
    (V : Set (Coeff p × Coeff p)) (hV : IsOpen V) (hbase : 0 ∈ V)
    (hf : AnalyticOnNhd ℂ f V)
    (hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (hrot : ∀ z ∈ V, ∀ k ∉ S,
      fderiv ℂ f z (actionRotationVectorCLM p k z) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → Coeff r,
      IsOpen Z ∧ 0 ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧
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
  exact exists_local_tail_sum_factor_of_recovery hp S f G V hV hbase hG he hsplit

/-- Tail actions and the unsquared finite head admit a common analytic
factor in the entire sequence target norm, including at the origin. -/
theorem exists_local_tail_action_factor (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hrot : ∀ z ∈ ball 0 R, ∀ k ∉ S,
      fderiv ℂ f z (actionRotationVectorCLM p k z) = 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (TailSumSpace q S),
      ∃ g : TailSumSpace q S → Coeff r,
      IsOpen Z ∧ 0 ∈ Z ∧ Z ⊆ ball 0 R ∧ IsOpen T ∧
      (fun z => tailSumCLM S (pairMixedSquare S z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      ∀ z ∈ Z, g (tailSumCLM S (pairMixedSquare S z)) = f z := by
  let V := ball (0 : Coeff p × Coeff p) (R/2)
  have hV : IsOpen V := isOpen_ball
  have hVsub : V ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z :=
    pairSignChange_invariant_of_tail_rotation_stationary hp S f R hR hf hrot
  obtain ⟨Z,T,g,hZ,h0Z,hZV,hT,himage,hg,he⟩ :=
    exists_local_tail_action_factor_of_sign_invariance (q := q) hp S f V hV
      (mem_ball_self (by positivity)) (hf.mono hVsub) hsign
      (fun z hz => hrot z (hVsub hz))
  exact ⟨Z,T,g,hZ,h0Z,hZV.trans hVsub,hT,himage,hg,he⟩

end NLS.Coeff
