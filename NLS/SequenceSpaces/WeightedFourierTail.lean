import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.ShiftedPairNorm
import NLS.ZakharovShabat.WeightedResonance

/-!
# The weighted Fourier remainder used in Lemma 6.5

The tail retains the boundary `|k|=N`, as in the source. It contracts the exact
finite-exponent pair norm and converges to zero. The signs in the physical
pair do not change a symmetric cutoff.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted symmetric tail, including its boundary. -/
def fourierTail (w : Weight) (N : ℕ) : WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  ZakharovShabat.weightedMask w (fun k => N ≤ k.natAbs)

@[simp] theorem fourierTail_apply (w : Weight) (N : ℕ) (a : WeightedCoeff w p) (k : ℤ) :
    (fourierTail w N a).val k = if N ≤ k.natAbs then a.val k else 0 :=
  ZakharovShabat.weightedMask_apply _ _ _ _

theorem weightEquiv_fourierTail (w : Weight) (N : ℕ) (a : WeightedCoeff w p) :
    weightEquiv w p (fourierTail w N a) = Coeff.fourierTail N (weightEquiv w p a) := by
  ext k
  simp only [weightEquiv_apply, fourierTail_apply, Coeff.fourierTail_apply]
  split_ifs <;> simp

theorem norm_fourierTail_le (w : Weight) (N : ℕ) (a : WeightedCoeff w p) :
    ‖fourierTail w N a‖ ≤ ‖a‖ := ZakharovShabat.norm_weightedMask_le _ _ _

@[simp] theorem fourierTail_zero (w : Weight) (a : WeightedCoeff w p) : fourierTail w 0 a = a := by
  apply Subtype.ext
  funext k
  simp

@[simp] theorem fourierTail_fourierTail (w : Weight) (M N : ℕ) (a : WeightedCoeff w p) :
    fourierTail w M (fourierTail w N a) = fourierTail w (max M N) a := by
  apply Subtype.ext
  funext k
  by_cases hM : M ≤ k.natAbs <;> by_cases hN : N ≤ k.natAbs <;> simp [hM, hN]

theorem tendsto_fourierTail (hp : p ≠ ⊤) (w : Weight) (a : WeightedCoeff w p) :
    Filter.Tendsto (fun N : ℕ => fourierTail w N a) Filter.atTop (nhds 0) := by
  have h := ((weightIsometry w p).symm.continuous.tendsto 0).comp (Coeff.tendsto_fourierTail hp (weightEquiv w p a))
  have he (N : ℕ) : (weightIsometry w p).symm (Coeff.fourierTail N (weightEquiv w p a)) = fourierTail w N a := by
    apply (weightIsometry w p).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (weightEquiv_fourierTail w N a).symm
  simpa only [Function.comp_def, he, map_zero] using h

end NLS.WeightedCoeff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's remainder on both physical components, in its exact pair norm. -/
def weightedPairFourierTail (w : Weight) (N : ℕ) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair w p :=
  WeightedCoeffPair.mapComponents w w (WeightedCoeff.fourierTail w N) (WeightedCoeff.fourierTail w N)

@[simp] theorem weightedPairFourierTail_fst (w : Weight) (N : ℕ) (f : WeightedCoeffPair w p) :
    (weightedPairFourierTail w N f).fst = WeightedCoeff.fourierTail w N f.fst := rfl
@[simp] theorem weightedPairFourierTail_snd (w : Weight) (N : ℕ) (f : WeightedCoeffPair w p) :
    (weightedPairFourierTail w N f).snd = WeightedCoeff.fourierTail w N f.snd := rfl

theorem norm_weightedPairFourierTail_le (hp : p ≠ ⊤) (w : Weight) (N : ℕ) (f : WeightedCoeffPair w p) :
    ‖weightedPairFourierTail w N f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using! WeightedCoeffPair.norm_mapComponents_le hp w w
    (WeightedCoeff.fourierTail w N) (WeightedCoeff.fourierTail w N) zero_le_one
    (fun a => by simpa using WeightedCoeff.norm_fourierTail_le w N a)
    (fun a => by simpa using WeightedCoeff.norm_fourierTail_le w N a) f

theorem tendsto_weightedPairFourierTail (hp : p ≠ ⊤) (w : Weight) (f : WeightedCoeffPair w p) :
    Filter.Tendsto (fun N : ℕ => weightedPairFourierTail w N f) Filter.atTop (nhds 0) := by
  have h := (WeightedCoeff.tendsto_fourierTail hp w f.fst).prodMk_nhds
    (WeightedCoeff.tendsto_fourierTail hp w f.snd)
  exact ((WeightedCoeffPair.toMax w p).symm.continuous.tendsto 0).comp h

end NLS.ZakharovShabat
