import NLS.ZakharovShabat.WeightedResonance
import NLS.SequenceSpaces.ShiftedWeight
import NLS.ZakharovShabat.Operator

/-!
# The free pencil on the weighted one-derivative domain

Multiplying a weight by `1+|k|` gives the domain of the weighted free pencil.
The coefficient-preserving inclusions identify it with the already constructed
free differential operator whenever the original weight is at least one.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Add one Fourier derivative to an arbitrary positive weight. -/
def Weight.oneDerivative (w : Weight) : Weight :=
  ⟨fun k => w k * (1 + |(k : ℝ)|), fun k => mul_pos (w.positive k) (by positivity)⟩

@[simp] theorem Weight.oneDerivative_apply (w : Weight) (k : ℤ) :
    w.oneDerivative k = w k * (1 + |(k : ℝ)|) := rfl

theorem Weight.le_oneDerivative (w : Weight) (k : ℤ) : w k ≤ w.oneDerivative k := by
  change w k ≤ w k * (1 + |(k : ℝ)|)
  nlinarith [w.positive k, abs_nonneg (k : ℝ)]

namespace ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

abbrev WeightedDomain (w : Weight) (p : ℝ≥0∞) := WeightedCoeffPair w.oneDerivative p

/-- Reflect the first physical Fourier index into the source's signed index. -/
def freeFrequency (b : Bool) (k : ℤ) : ℤ := if b then -k else k

@[simp] theorem freeFrequency_true (k : ℤ) : freeFrequency true k = -k := rfl
@[simp] theorem freeFrequency_false (k : ℤ) : freeFrequency false k = k := rfl
@[simp] theorem abs_freeFrequency (b : Bool) (k : ℤ) :
    |(freeFrequency b k : ℝ)| = |(k : ℝ)| := by cases b <;> simp [freeFrequency]

theorem norm_freeDenominator_le (z : ℂ) (b : Bool) (k : ℤ) :
    ‖z - (Real.pi : ℂ) * freeFrequency b k‖ ≤ (‖z‖ + Real.pi) * (1 + |(k : ℝ)|) := by
  have h := norm_sub_le z ((Real.pi : ℂ) * freeFrequency b k)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_intCast, abs_freeFrequency] at h
  nlinarith [norm_nonneg z, Real.pi_pos, abs_nonneg (k : ℝ)]

/-- One component of `λ-L₀`, from the weighted derivative domain to its base. -/
def weightedScalarPencil (w : Weight) (z : ℂ) (b : Bool) :
    WeightedCoeff w.oneDerivative p →L[ℂ] WeightedCoeff w p :=
  WeightedCoeff.weightedMultiplierCLM w.oneDerivative w
    (fun k => z - (Real.pi : ℂ) * freeFrequency b k) (‖z‖ + Real.pi)
    (by positivity) (fun k => by
      have h := mul_le_mul_of_nonneg_left (norm_freeDenominator_le z b k) (w.positive k).le
      simpa only [Weight.oneDerivative_apply, mul_left_comm] using h)

@[simp] theorem weightedScalarPencil_apply (w : Weight) (z : ℂ) (b : Bool)
    (a : WeightedCoeff w.oneDerivative p) (k : ℤ) :
    (weightedScalarPencil w z b a).val k = (z - (Real.pi : ℂ) * freeFrequency b k) * a.val k := rfl

/-- The two signed components of the weighted free pencil. -/
def weightedFreePencil (w : Weight) (z : ℂ) : WeightedDomain w p →L[ℂ] WeightedCoeffPair w p :=
  WeightedCoeffPair.mapComponents w.oneDerivative w (weightedScalarPencil w z true) (weightedScalarPencil w z false)

@[simp] theorem weightedFreePencil_fst (w : Weight) (z : ℂ) (a : WeightedDomain w p) (k : ℤ) :
    (weightedFreePencil w z a).fst.val k = (z + (Real.pi : ℂ) * k) * a.fst.val k := by
  change (z - (Real.pi : ℂ) * (-k : ℤ)) * a.fst.val k = _
  simp
@[simp] theorem weightedFreePencil_snd (w : Weight) (z : ℂ) (a : WeightedDomain w p) (k : ℤ) :
    (weightedFreePencil w z a).snd.val k = (z - (Real.pi : ℂ) * k) * a.snd.val k := rfl

/-- Coefficient-preserving weighted domain inclusion. -/
def weightedDomainInclusion (w : Weight) : WeightedDomain w p →L[ℂ] WeightedCoeffPair w p :=
  WeightedCoeffPair.mapComponents w.oneDerivative w
    (WeightedCoeff.inclusionCLM _ _ w.le_oneDerivative) (WeightedCoeff.inclusionCLM _ _ w.le_oneDerivative)

@[simp] theorem weightedDomainInclusion_fst (w : Weight) (a : WeightedDomain w p) (k : ℤ) :
    (weightedDomainInclusion w a).fst.val k = a.fst.val k := WeightedCoeff.inclusionCLM_apply _ _ w.le_oneDerivative _ _
@[simp] theorem weightedDomainInclusion_snd (w : Weight) (a : WeightedDomain w p) (k : ℤ) :
    (weightedDomainInclusion w a).snd.val k = a.snd.val k := WeightedCoeff.inclusionCLM_apply _ _ w.le_oneDerivative _ _

theorem weightedDomainInclusion_injective (w : Weight) : Function.Injective (weightedDomainInclusion (p := p) w) := by
  intro a b h
  apply weightedPair_ext
  · intro k; simpa using congrArg (fun a => a.fst.val k) h
  · intro k; simpa using congrArg (fun a => a.snd.val k) h

/-- Forget the spectral weight in the base space, preserving physical coefficients. -/
def weightedBaseToPair (w : SpectralWeight) : WeightedCoeffPair w.toWeight p →L[ℂ] PairSpace p :=
  ((SpectralWeight.toCoeff w).prodMap (SpectralWeight.toCoeff w)).comp
    (WeightedCoeffPair.toMax w.toWeight p).toContinuousLinearMap

@[simp] theorem weightedBaseToPair_fst (w : SpectralWeight) (a : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedBaseToPair w a).1 k = a.fst.val k := by
  change SpectralWeight.toCoeff w a.fst k = a.fst.val k
  exact SpectralWeight.toCoeff_apply w _ _
@[simp] theorem weightedBaseToPair_snd (w : SpectralWeight) (a : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedBaseToPair w a).2 k = a.snd.val k := by
  change SpectralWeight.toCoeff w a.snd k = a.snd.val k
  exact SpectralWeight.toCoeff_apply w _ _

theorem sobolev_le_spectral_oneDerivative (w : SpectralWeight) (k : ℤ) :
    Weight.sobolev 1 k ≤ w.toWeight.oneDerivative k := by
  simp only [Weight.sobolev_apply, Real.rpow_one, Weight.oneDerivative_apply]
  nlinarith [w.one_le k, abs_nonneg (k : ℝ)]

/-- Forget the spectral weight in the derivative domain. -/
def weightedDomainToDomain (w : SpectralWeight) : WeightedDomain w.toWeight p →L[ℂ] Domain p :=
  ((WeightedCoeff.inclusionCLM _ _ (sobolev_le_spectral_oneDerivative w)).prodMap
    (WeightedCoeff.inclusionCLM _ _ (sobolev_le_spectral_oneDerivative w))).comp
    (WeightedCoeffPair.toMax w.toWeight.oneDerivative p).toContinuousLinearMap

@[simp] theorem weightedDomainToDomain_fst (w : SpectralWeight) (a : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainToDomain w a).1.val k = a.fst.val k := WeightedCoeff.inclusionCLM_apply _ _ (sobolev_le_spectral_oneDerivative w) _ _
@[simp] theorem weightedDomainToDomain_snd (w : SpectralWeight) (a : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainToDomain w a).2.val k = a.snd.val k := WeightedCoeff.inclusionCLM_apply _ _ (sobolev_le_spectral_oneDerivative w) _ _

/-- The weighted pencil is the restriction of the original free differential pencil. -/
theorem weightedFreePencil_eq_original (w : SpectralWeight) (z : ℂ) (a : WeightedDomain w.toWeight p) :
    weightedBaseToPair w (weightedFreePencil w.toWeight z a) =
      z • domainInclusion (weightedDomainToDomain w a) - freeOperator (weightedDomainToDomain w a) := by
  apply Prod.ext <;> ext k
  · change _ = z * (scalarInclusion (weightedDomainToDomain w a).1) k - (freeOperator (weightedDomainToDomain w a)).1 k
    simp only [weightedBaseToPair_fst, weightedFreePencil_fst, scalarInclusion_apply, freeOperator_fst_apply, weightedDomainToDomain_fst]
    ring
  · change _ = z * (scalarInclusion (weightedDomainToDomain w a).2) k - (freeOperator (weightedDomainToDomain w a)).2 k
    simp only [weightedBaseToPair_snd, weightedFreePencil_snd, scalarInclusion_apply, freeOperator_snd_apply, weightedDomainToDomain_snd]
    ring

end ZakharovShabat
end NLS
