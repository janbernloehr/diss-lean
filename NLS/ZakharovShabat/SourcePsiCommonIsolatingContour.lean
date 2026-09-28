import NLS.ZakharovShabat.SourcePsiEquationChartCompatibility
import NLS.ZakharovShabat.SourceCriticalRootRatioEnclosingCircle

/-!
# Common outer contours inside one isolating-disc family

Two filled contour discs compactly contained in the same assigned
open isolating disc fit inside a slightly larger circle that remains
in that disc. The larger circle encloses the selected gap and avoids
every other gap. This supplies the concrete geometric hypothesis for
compatibility of selected psi equation charts.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem exists_common_outer_circle_within_ball
    (C : ℂ) (S : ℝ) (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 ≤ r₀)
    (h₀ : closedBall c₀ r₀ ⊆ ball C S)
    (h₁ : closedBall c₁ r₁ ⊆ ball C S) :
    ∃ R : ℝ, 0 < R ∧
      closedBall c₀ r₀ ⊆ ball C R ∧
      closedBall c₁ r₁ ⊆ ball C R ∧
      closedBall C R ⊆ ball C S := by
  let K : Set ℂ := closedBall c₀ r₀ ∪ closedBall c₁ r₁
  have hK : IsCompact K :=
    (isCompact_closedBall c₀ r₀).union (isCompact_closedBall c₁ r₁)
  have hKne : K.Nonempty :=
    ⟨c₀,Or.inl (mem_closedBall_self hr₀)⟩
  have hdist : Continuous (fun w : ℂ => dist w C) :=
    continuous_dist.comp (continuous_id.prodMk continuous_const)
  obtain ⟨z,hz,hmax⟩ :=
    hK.exists_isMaxOn hKne hdist.continuousOn
  have hzS : dist z C < S := by
    rcases hz with hz₀ | hz₁
    · exact mem_ball.mp (h₀ hz₀)
    · exact mem_ball.mp (h₁ hz₁)
  let R := (dist z C + S)/2
  have hmaxR : dist z C < R := by dsimp [R]; linarith
  have hRS : R < S := by dsimp [R]; linarith
  have hR : 0 < R := by
    have := dist_nonneg (x := z) (y := C)
    linarith
  refine ⟨R,hR,?_,?_,closedBall_subset_ball hRS⟩
  · intro w hw
    exact mem_ball.mpr (lt_of_le_of_lt (hmax (Or.inl hw)) hmaxR)
  · intro w hw
    exact mem_ball.mpr (lt_of_le_of_lt (hmax (Or.inr hw)) hmaxR)

/-- If two contour families enclose the same moving gaps and their
filled discs lie in one assigned isolating-disc family, they are
comparable through common outer circles. -/
theorem sourcePsiContourFamiliesComparable_of_common_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ,
      sourceSpectralCluster hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (hR₀ : ∀ m, 0 < R₀ m) (hR₁ : ∀ m, 0 < R₁ m)
    (hseg₀ : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₀ m) (R₀ m))
    (hseg₁ : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₁ m) (R₁ m))
    (hfill₀ : ∀ m, closedBall (c₀ m) (R₀ m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hfill₁ : ∀ m, closedBall (c₁ m) (R₁ m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m) :
    sourcePsiContourFamiliesComparable hp hp1 ψ c₀ c₁ R₀ R₁ := by
  intro m
  let C := sourceIsolatingCenter hp hp1 φ N m
  let S := sourceIsolatingRadius hp hp1 φ N ε m
  have h₀ : closedBall (c₀ m) (R₀ m) ⊆ ball C S := by
    simpa only [C,S,← sourceIsolatingDisc_eq_ball] using hfill₀ m
  have h₁ : closedBall (c₁ m) (R₁ m) ⊆ ball C S := by
    simpa only [C,S,← sourceIsolatingDisc_eq_ball] using hfill₁ m
  obtain ⟨R,hR,hinside₀,hinside₁,hinside⟩ :=
    exists_common_outer_circle_within_ball
      C S (c₀ m) (c₁ m) (R₀ m) (R₁ m) (hR₀ m).le h₀ h₁
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball C R :=
    (hseg₀ m).trans (ball_subset_closedBall.trans hinside₀)
  have houterIso : closedBall C R ⊆
      sourceIsolatingDisc hp hp1 φ N ε m := by
    simpa only [C,S,sourceIsolatingDisc_eq_ball] using hinside
  have hother : closedBall C R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m :=
    houterIso.trans (sourceIsolatingDisc_subset_omittedDomain
      hp hp1 φ ψ N ε hcluster hdisjoint m)
  exact ⟨C,R,hR₀ m,hR₁ m,hR,hseg₀ m,hseg₁ m,hseg,
    hinside₀.trans ball_subset_closedBall,
    hinside₁.trans ball_subset_closedBall,hother⟩

/-- Two selected psi equations agree when their contours fit in the
same isolating-disc family and both have their scalar coordinate
formulas at the given root and source inputs. -/
theorem sourcePsiSelectedEquationSequence_eq_of_common_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ,
      sourceSpectralCluster hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) (a : DeletedCoeff p n)
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (hR₀ : ∀ m, 0 < R₀ m) (hR₁ : ∀ m, 0 < R₁ m)
    (hseg₀ : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₀ m) (R₀ m))
    (hseg₁ : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₁ m) (R₁ m))
    (hfill₀ : ∀ m, closedBall (c₀ m) (R₀ m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hfill₁ : ∀ m, closedBall (c₁ m) (R₁ m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hcoord₀ : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c₀ m) (R₀ m))
    (hcoord₁ : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c₁ m) (R₁ m)) :
    sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a ψ =
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ a ψ := by
  exact sourcePsiSelectedEquationSequence_eq_of_comparable_contours
    hp hp1 n a ψ c₀ c₁ R₀ R₁ hcoord₀ hcoord₁
    (sourcePsiContourFamiliesComparable_of_common_isolatingDiscs
      hp hp1 φ ψ N ε hcluster hdisjoint c₀ c₁ R₀ R₁
      hR₀ hR₁ hseg₀ hseg₁ hfill₀ hfill₁)

end NLS.ZakharovShabat
