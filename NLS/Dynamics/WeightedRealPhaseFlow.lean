import NLS.Dynamics.PhaseAlmostPeriodic
import NLS.SequenceSpaces.WeightedRealInclusion

/-! # Hamiltonian phase recurrence in native weighted real pairs

The actual weighted norms and original coefficients are retained throughout.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Normalized real coordinates for native weighted pairs. -/
def weightedRealCoordinates (w : Weight) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) ≃L[ℝ]
      (RealCoeff p × RealCoeff p) :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).trans
    ((WeightedRealCoeff.weightEquiv w p).prodCongr (WeightedRealCoeff.weightEquiv w p))

/-- Hamiltonian phase rotation on the actual weighted real target. -/
def weightedRealPhaseFlow (w : Weight) (ω : ℤ → ℝ) (t : ℝ)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  (weightedRealCoordinates w).symm
    (decodeReal (hamiltonianPhaseFlow ω t (encodeReal (weightedRealCoordinates w z))))

/-- Uniform recurrence holds in the native weighted pair norm. -/
theorem bohrAlmostPeriodic_weightedRealPhaseFlow (w : Weight) (hp : p ≠ ⊤)
    (ω : ℤ → ℝ) (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    Dynamics.BohrAlmostPeriodic (fun t : ℝ => weightedRealPhaseFlow w ω t z) :=
  bohrAlmostPeriodic_hamiltonianPhaseFlow_comp hp ω
    (encodeReal (weightedRealCoordinates w z))
    (fun a => (weightedRealCoordinates w).symm (decodeReal a))
    ((weightedRealCoordinates w).symm.continuous.comp decodeReal.continuous)

/-- Real Hamiltonian rotation is linear in each pair of coefficients, with
the same multiplier in both components. -/
theorem realPhase_coordinate_mul (ω : ℤ → ℝ) (t : ℝ)
    (a b : RealCoeff p × RealCoeff p) (n : ℤ) (r : ℝ)
    (h₁ : a.1 n = r*b.1 n) (h₂ : a.2 n = r*b.2 n) :
    (decodeReal (hamiltonianPhaseFlow ω t (encodeReal a))).1 n =
      r*(decodeReal (hamiltonianPhaseFlow ω t (encodeReal b))).1 n ∧
    (decodeReal (hamiltonianPhaseFlow ω t (encodeReal a))).2 n =
      r*(decodeReal (hamiltonianPhaseFlow ω t (encodeReal b))).2 n := by
  have encode_fst (z : RealCoeff p × RealCoeff p) :
      (encodeReal z).1 n = complexCoordinateScale*((z.1 n : ℂ)-Complex.I*(z.2 n : ℂ)) := by
    change (rectangularToComplex (RealCoeff.complexCLM p z.1,RealCoeff.complexCLM p z.2)).1 n = _
    exact rectangularToComplex_fst _ n
  have encode_snd (z : RealCoeff p × RealCoeff p) :
      (encodeReal z).2 n = complexCoordinateScale*((z.1 n : ℂ)+Complex.I*(z.2 n : ℂ)) := by
    change (rectangularToComplex (RealCoeff.complexCLM p z.1,RealCoeff.complexCLM p z.2)).2 n = _
    exact rectangularToComplex_snd _ n
  have decode_fst (z : Coeff p × Coeff p) :
      (decodeReal z).1 n = (complexCoordinateScale*(z.1 n+z.2 n)).re := by
    change ((rectangularToComplex.symm z).1 n).re = _
    rw [rectangularToComplex_symm_fst]
  have decode_snd (z : Coeff p × Coeff p) :
      (decodeReal z).2 n = (Complex.I*complexCoordinateScale*(z.1 n-z.2 n)).re := by
    change ((rectangularToComplex.symm z).2 n).re = _
    rw [rectangularToComplex_symm_snd]
  have mul_re (c : ℂ) : r*c.re = ((r:ℂ)*c).re := by simp [Complex.mul_re]
  constructor <;>
    simp only [decode_fst,decode_snd,hamiltonianPhaseFlow_fst,hamiltonianPhaseFlow_snd,
      encode_fst,encode_snd,h₁,h₂,Complex.ofReal_mul] <;>
    rw [mul_re] <;> congr 1 <;> ring


/-- Normalized and raw real target coordinates differ by the actual weight. -/
theorem weightedRealCoordinates_raw (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    (weightedRealCoordinates w a).1 n = w n*(WeightedRealCoeff.forgetPairWeightCLM w hw a).1 n ∧
    (weightedRealCoordinates w a).2 n = w n*(WeightedRealCoeff.forgetPairWeightCLM w hw a).2 n := by
  constructor
  · change ((w n:ℂ)*a.fst.val.val n).re = w n*(WeightedRealCoeff.forgetWeightCLM w hw a.fst n)
    rw [WeightedRealCoeff.forgetWeightCLM_apply]
    simp [Complex.mul_re]
  · change ((w n:ℂ)*a.snd.val.val n).re = w n*(WeightedRealCoeff.forgetWeightCLM w hw a.snd n)
    rw [WeightedRealCoeff.forgetWeightCLM_apply]
    simp [Complex.mul_re]

/-- Forgetting the weight gives exactly the original Hamiltonian phase rotation. -/
theorem forget_weightedRealPhaseFlow (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (ω : ℤ → ℝ) (t : ℝ)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    WeightedRealCoeff.forgetPairWeightCLM w hw (weightedRealPhaseFlow w ω t a) =
      decodeReal (hamiltonianPhaseFlow ω t
        (encodeReal (WeightedRealCoeff.forgetPairWeightCLM w hw a))) := by
  have h (n : ℤ) := realPhase_coordinate_mul ω t (weightedRealCoordinates w a)
    (WeightedRealCoeff.forgetPairWeightCLM w hw a) n (w n)
    (weightedRealCoordinates_raw w hw a n).1 (weightedRealCoordinates_raw w hw a n).2
  have he : weightedRealCoordinates w (weightedRealPhaseFlow w ω t a) =
      decodeReal (hamiltonianPhaseFlow ω t (encodeReal (weightedRealCoordinates w a))) :=
    (weightedRealCoordinates w).apply_symm_apply _
  apply Prod.ext <;> apply lp.ext <;> funext n
  · have hraw := (weightedRealCoordinates_raw w hw (weightedRealPhaseFlow w ω t a) n).1
    rw [he] at hraw
    exact mul_left_cancel₀ (w.positive n).ne' (hraw.symm.trans (h n).1)
  · have hraw := (weightedRealCoordinates_raw w hw (weightedRealPhaseFlow w ω t a) n).2
    rw [he] at hraw
    exact mul_left_cancel₀ (w.positive n).ne' (hraw.symm.trans (h n).2)


end NLS.Birkhoff
