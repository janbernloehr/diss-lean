import NLS.ZakharovShabat.SourceBirkhoffActionAngleMap
import NLS.ZakharovShabat.SourceSection14

/-! # Constructed Section 14 action-angle maps

One constructed original family supplies the literal real formulas and
the analytic sequence map. At the Hilbert exponent it gives a global
analytic homeomorphism with the same formulas for any admissible eta
choice. These are internal identities, not an identification with a
separately formalized external book construction.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ComplexOrder
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct a full literal action-angle map with its original family and analytic inverse. -/
theorem sourceSection14_actionAngle_map (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ _D : SourceSection14Data hp hp1 W₀ W V s,
      ∃ F : realTypeSourceSubmodule p → RealCoeff p × RealCoeff p,
        (∀ φ n, (F φ).1 n = Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
          Real.cos (sourceAngularOriginalTheta hp hp1 n s φ.val).re ∧
          (F φ).2 n = Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
          Real.sin (sourceAngularOriginalTheta hp hp1 n s φ.val).re) ∧
        F = sourceRealBirkhoffMap hp hp1 s ∧ AnalyticOnNhd ℝ F univ ∧
        (p ≤ 2 → ∃ e : realTypeSourceSubmodule p ≃ₜ (RealCoeff p × RealCoeff p),
          (∀ φ, e φ = F φ) ∧ AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  let A := D.toSourceSection14OriginalData
  refine ⟨W₀,W,V,s,D,A.realActionAngleMap,fun φ n => ⟨rfl,rfl⟩,
    A.realActionAngleMap_eq,A.realActionAngleMap_analytic,?_⟩
  intro hp2
  exact ⟨A.realActionAngleHomeomorph hp2,fun _ => rfl,A.realActionAngleHomeomorph_analytic hp2⟩

/-- At the Hilbert exponent the constructed global map has the literal formulas
for every normalized eta choice, including arbitrary values at collapsed gaps. -/
theorem sourceSection14_hilbert_actionAngle_inverse :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ _D : SourceSection14Data (by simp) (by norm_num) W₀ W V s,
      ∃ e : realTypeSourceSubmodule 2 ≃ₜ (RealCoeff 2 × RealCoeff 2),
        (∀ φ, e φ = sourceRealBirkhoffMap (by simp) (by norm_num) s φ) ∧
        AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
        ∀ (φ : realTypeSourceSubmodule 2) (n : ℤ) (v : ℂ),
          (sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n ≠ 0 →
            v ∈ sourceAngularOriginalEtaIntegralValues (by simp) (by norm_num) n s φ.val) →
          (e φ).1 n = Real.sqrt (2*(sourceIndexedAction (by simp) (by norm_num) n φ.val).re)*
            Real.cos (v+sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val).re ∧
          (e φ).2 n = Real.sqrt (2*(sourceIndexedAction (by simp) (by norm_num) n φ.val).re)*
            Real.sin (v+sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val).re := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  refine ⟨W₀,W,V,s,D,A.realActionAngleHomeomorph le_rfl,?_,
    (A.realActionAngleHomeomorph_analytic le_rfl).1,
    (A.realActionAngleHomeomorph_analytic le_rfl).2,?_⟩
  · intro φ
    exact congrFun A.realActionAngleMap_eq φ
  · intro φ n v hv
    change (A.realActionAngleMap φ).1 n = _ ∧ (A.realActionAngleMap φ).2 n = _
    rw [A.realActionAngleMap_eq]
    exact A.real_rectangular_formula_of_eta φ n v hv

end NLS.ZakharovShabat
