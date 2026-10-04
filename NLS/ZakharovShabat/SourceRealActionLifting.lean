import NLS.SequenceSpaces.RealActionLifting
import NLS.ZakharovShabat.SourceBirkhoffInverseChart

/-! # Real lifts in actual source charts

A sufficiently small action ball has real representatives in any prescribed
Birkhoff neighborhood. Real action invariance then identifies a local
analytic factor with its value at every real source having the same actions.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B X : Set (CoeffPair p)}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

namespace SourceBirkhoffMapComplexData

/-- The actual action sequence at a real source is nonnegative real. -/
theorem actionSequence_mem_nonnegativeLocus
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) :
    sourceActionSequence (q := q) hp hp1 t φ.val ∈ Coeff.nonnegativeLocus q :=
  Coeff.quadraticActions_mem_nonnegativeLocus _ ((Coeff.mem_realPairLocus_iff _).mpr
    ⟨sourceRealBirkhoffMap hp hp1 t φ, D.real_map_complex_inclusion φ⟩)

/-- Equality of the Banach action sequences gives equality of all real actions. -/
theorem mem_actionLevelSet_of_actionSequence_eq
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ ψ : realTypeSourceSubmodule p)
    (he : sourceActionSequence (q := q) hp hp1 t ψ.val = sourceActionSequence (q := q) hp hp1 t φ.val) :
    ψ ∈ sourceRealActionLevelSet hp hp1 φ := by
  intro n
  have h := congrArg (fun b : Coeff q => (b n).re) he
  simpa only [D.actionSequence_apply ψ.val (D.real_subset ψ.property),
    D.actionSequence_apply φ.val (D.real_subset φ.property),
    sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property,
    sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property] using h

/-- Restrict an action neighborhood so every nonnegative action has a real
lift in the chosen original neighborhood, uniformly for all target maps. -/
theorem exists_realAction_ball
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p)
    (Z : Set (Coeff p × Coeff p)) (hZ : IsOpen Z)
    (hz : sourceBirkhoffMap hp hp1 t φ.val ∈ Z)
    (T : Set (Coeff q)) (hT : IsOpen T) (hc : sourceActionSequence (q := q) hp hp1 t φ.val ∈ T) :
    ∃ r : ℝ, 0 < r ∧ ball (sourceActionSequence (q := q) hp hp1 t φ.val) r ⊆ T ∧
      ball (sourceActionSequence (q := q) hp hp1 t φ.val) r ∩ Coeff.nonnegativeLocus q ⊆
        quadraticActionsExponent (q := q) '' (Z ∩ Coeff.realPairLocus p) := by
  have hzr : sourceBirkhoffMap hp hp1 t φ.val ∈ Coeff.realPairLocus p :=
    (Coeff.mem_realPairLocus_iff _).mpr
      ⟨sourceRealBirkhoffMap hp hp1 t φ, D.real_map_complex_inclusion φ⟩
  obtain ⟨r, hr, hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (q := q) hp _ hzr Z hZ hz
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hT _ hc
  exact ⟨min r s, lt_min hr hs, (ball_subset_ball (min_le_right _ _)).trans hball,
    (inter_subset_inter_left _ (ball_subset_ball (min_le_left _ _))).trans hlift⟩

end SourceBirkhoffMapComplexData
namespace SourceBirkhoffInverseChart
variable {D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t}
  {φ : realTypeSourceSubmodule p} {U : Set (CoeffPair p)}

/-- A local factor recovering a real action invariant source function agrees
with that function at any real source whose actions have a local real lift. -/
theorem recover_of_real_action_lift {F : Type*}
    (C : SourceBirkhoffInverseChart D φ U)
    (Z : Set (Coeff p × Coeff p)) (hZC : Z ⊆ C.target)
    (f : CoeffPair p → F) (G : Coeff q → F)
    (hinv : ∀ a b : realTypeSourceSubmodule p, b ∈ sourceRealActionLevelSet hp hp1 a →
      f b.val = f a.val)
    (hrec : ∀ z ∈ Z, G (quadraticActionsExponent z) = f (C.inverse z))
    (ψ : realTypeSourceSubmodule p)
    (hlift : sourceActionSequence (q := q) hp hp1 t ψ.val ∈
      quadraticActionsExponent (q := q) '' (Z ∩ Coeff.realPairLocus p)) :
    G (sourceActionSequence (q := q) hp hp1 t ψ.val) = f ψ.val := by
  obtain ⟨z, ⟨hz, hzr⟩, he⟩ := hlift
  have hreal : C.inverse z ∈ realTypeSourceLocus p := by
    obtain ⟨w, hw⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
    rw [← hw]
    exact C.real_preserving w (hw.symm ▸ hZC hz)
  let χ : realTypeSourceSubmodule p := ⟨C.inverse z, hreal⟩
  have hχ : sourceActionSequence (q := q) hp hp1 t χ.val = sourceActionSequence (q := q) hp hp1 t ψ.val :=
    (C.actionSequence_eq z (hZC hz)).trans he
  calc
    G (sourceActionSequence (q := q) hp hp1 t ψ.val) = G (quadraticActionsExponent z) := by rw [he]
    _ = f (C.inverse z) := hrec z hz
    _ = f ψ.val := hinv ψ χ (D.mem_actionLevelSet_of_actionSequence_eq ψ χ hχ)

end SourceBirkhoffInverseChart
end NLS.ZakharovShabat
