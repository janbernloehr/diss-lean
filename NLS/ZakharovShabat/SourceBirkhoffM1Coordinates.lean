import NLS.ZakharovShabat.SourceM1WeightedActionEstimate
import NLS.ZakharovShabat.SourceBirkhoffTheorem15_2
import NLS.SequenceSpaces.RealHilbertPairFromSquares

/-! # The actual Birkhoff map in every M₁ weighted sequence space

Multiplication of the original rectangular coordinates by w(2n) produces
an actual real Hilbert pair. Its squared norm is exactly twice the weighted
action sum. In particular the target membership is proved, not assumed.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The real original source represented by normalized weighted coordinates. -/
def normalizedWeightedRealSource (w : SpectralWeight) (a : realTypeSourceSubmodule 2) :
    realTypeSourceSubmodule 2 :=
  ⟨normalizedWeightedSource w a.val, normalizedWeightedSource_realType w a.val a.property⟩

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The weighted rectangular radius identity for an arbitrary spectral weight. -/
theorem real_map_M1_weighted_radius
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (ψ : realTypeSourceSubmodule 2) (n : ℤ) :
    (w (2*n)*(sourceRealBirkhoffMap (by simp) (by norm_num) s ψ).1 n)^2 +
      (w (2*n)*(sourceRealBirkhoffMap (by simp) (by norm_num) s ψ).2 n)^2 =
      2*sourceM1ActionTerm w ψ.val n := by
  simp only [mul_pow,sourceM1ActionTerm,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property,
    norm_sourceRealAction]
  rw [← mul_add,D.real_map_action_radius ψ n]
  ring

/-- The weighted image of the actual Birkhoff map, with both components in ℓ². -/
def m1Coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : realTypeSourceSubmodule 2) :
    WithLp 2 (RealCoeff 2 × RealCoeff 2) :=
  realHilbertPairFromSquares
    (fun n => w (2*n)*(sourceRealBirkhoffMap (by simp) (by norm_num) s
      (normalizedWeightedRealSource w a)).1 n)
    (fun n => w (2*n)*(sourceRealBirkhoffMap (by simp) (by norm_num) s
      (normalizedWeightedRealSource w a)).2 n)
    (by
      have h := (sourceM1_real_weighted_actions_normalized w hw a).1.mul_left 2
      exact h.congr (fun n => (D.real_map_M1_weighted_radius w (normalizedWeightedRealSource w a) n).symm))

@[simp] theorem m1Coordinates_fst
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : realTypeSourceSubmodule 2) (n : ℤ) :
    (D.m1Coordinates w hw a).fst n = w (2*n)*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s (normalizedWeightedRealSource w a)).1 n := rfl

@[simp] theorem m1Coordinates_snd
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : realTypeSourceSubmodule 2) (n : ℤ) :
    (D.m1Coordinates w hw a).snd n = w (2*n)*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s (normalizedWeightedRealSource w a)).2 n := rfl

/-- Exact weighted Parseval identity, retaining the doubled frequency w(2n). -/
theorem m1Coordinates_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : realTypeSourceSubmodule 2) :
    ‖D.m1Coordinates w hw a‖^2 =
      2*(∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a.val) n) := by
  rw [m1Coordinates,realHilbertPairFromSquares_norm_sq,← tsum_mul_left]
  exact tsum_congr (fun n => D.real_map_M1_weighted_radius w (normalizedWeightedRealSource w a) n)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
