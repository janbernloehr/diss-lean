import NLS.ZakharovShabat.SourceM1ActionNeighborhood
import NLS.ZakharovShabat.SourceBirkhoffM1Estimate

/-! # Theorem 23.4 for the constructed Birkhoff map and original actions

The source and target use normalized weighted coordinates, with the exact
physical weight w(2n). A single Birkhoff map works for every M₁ weight.
The open action neighborhood contains the whole real weighted source locus.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both conclusions of Theorem 23.4, with the same positive constant in the
action and Birkhoff bounds. One may take c_w = 2048 for every M₁ weight. -/
theorem exists_sourceBirkhoffMap_theorem23_4 :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s,
        ∀ w : SpectralWeight, ∀ hw : w.HasLinearFactor,
          ∃ c : ℝ, 0 < c ∧ ∃ V : Set (CoeffPair 2), IsOpen V ∧ realTypeSourceLocus 2 ⊆ V ∧
            (∀ a ∈ V, Summable (sourceM1ActionTerm w (normalizedWeightedSource w a)) ∧
              (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a) n) ≤
                c^2*(w.realExtension (16*‖a‖^2))^2*‖a‖^2) ∧
            ∀ a : realTypeSourceSubmodule 2,
              ‖D.m1Coordinates w hw a‖ ≤ c*w.realExtension (16*‖a.val‖^2)*‖a.val‖ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : (1:ℝ≥0∞) < 2)
  refine ⟨W₀,B,W,s,D,?_⟩
  intro w hw
  obtain ⟨V,hV,hreal,hbound⟩ := exists_sourceM1Action_neighborhood w hw
  refine ⟨2048,by norm_num,V,hV,hreal,?_,fun a => D.m1Coordinates_norm_le w hw a⟩
  intro a ha
  refine ⟨(hbound a ha).1,(hbound a ha).2.trans ?_⟩
  gcongr
  norm_num

end NLS.ZakharovShabat
