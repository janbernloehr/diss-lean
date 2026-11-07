import NLS.Fourier.RealMeanZeroPeriodOne
import NLS.Fourier.PeriodicWeightedWeakStar
import NLS.Fourier.PeriodicEndpointLowerInclusion
import NLS.Dynamics.WeightedWeakStarPhaseFlow

/-!
# The article's original real pseudomeasure potentials

The parameter r denotes the Wiener predual order: the source potential has
regularity s=-r. The article range -1/2<s<=0 is therefore 0<=r<1/2.
Potential reality, zero mean and physical period one are properties of
original distributions on the period-two smooth test space.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- The exact source regularity interval, in predual-order coordinates. -/
def AdmissiblePredualOrder (r : ℝ) : Prop := 0 ≤ r ∧ r < 1/2

/-- Original real, mean-zero, physically one-periodic potentials of order -r. -/
def Potential (r : ℝ) :=
  {q : FourierLebesgueSpace (2:ℝ) (-r) ⊤ // q.val.IsRealMeanZeroPeriodOne}

/-- The same original potential represented in the coefficient Wiener weak dual. -/
def potentialCoordinates (r : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) :=
  WeightedCoeff.wienerDualRealization r (sobolevCoefficients (-r) ⊤ q)

@[simp] theorem potentialCoordinates_apply (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℤ) :
    WeightedCoeff.weakStarCoordinates r (potentialCoordinates r q) n = q.val (mode (-n)) := by
  simp only [potentialCoordinates, WeightedCoeff.weakStarCoordinates_wienerDualRealization,
    sobolevCoefficients_apply]

/-- Coordinate locus retaining both the real mean-zero and even-mode constraints. -/
def potentialCoordinateLocus (r : ℝ) :
    Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :=
  WeightedCoeff.realMeanZeroWeakStar r ∩
    {f | ∀ k : ℤ, WeightedCoeff.weakStarCoordinates r f (2*k+1) = 0}

/-- The coefficient constraints are exactly the physical distribution conditions. -/
theorem mem_potentialCoordinateLocus_iff (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    potentialCoordinates r q ∈ potentialCoordinateLocus r ↔ q.val.IsRealMeanZeroPeriodOne := by
  rw [Distribution.isRealMeanZeroPeriodOne_iff_coefficients]
  simp only [potentialCoordinateLocus, mem_inter_iff, WeightedCoeff.realMeanZeroWeakStar,
    mem_ofPred_eq, potentialCoordinates_apply, neg_zero, neg_neg]
  exact and_assoc

/-- The exact original Fourier norm survives the weak-star realization. -/
theorem norm_potentialCoordinates (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    ‖(potentialCoordinates r q).toStrongDual‖ = ‖q‖ := by
  simp only [potentialCoordinates, WeightedCoeff.norm_wienerDualRealization,
    LinearIsometryEquiv.norm_map]

/-- Recover an original smooth-test distribution from every full weak-dual point. -/
def potentialFromCoordinates (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    FourierLebesgueSpace (2:ℝ) (-r) ⊤ :=
  (sobolevCoefficients (-r) ⊤).symm (WeightedCoeff.weakStarCoeff r f)

@[simp] theorem potentialCoordinates_fromCoordinates (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    potentialCoordinates r (potentialFromCoordinates r f) = f := by
  simp only [potentialCoordinates, potentialFromCoordinates,
    LinearIsometryEquiv.apply_symm_apply, WeightedCoeff.wienerDualRealization_weakStarCoeff]

@[simp] theorem potentialFromCoordinates_coordinates (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    potentialFromCoordinates r (potentialCoordinates r q) = q := by
  simp only [potentialFromCoordinates, potentialCoordinates,
    WeightedCoeff.weakStarCoeff_wienerDualRealization, LinearIsometryEquiv.symm_apply_apply]

/-- The source potentials and the constrained full weak-dual locus are bijective. -/
def potentialCoordinateEquiv (r : ℝ) : Potential r ≃ potentialCoordinateLocus r where
  toFun q := ⟨potentialCoordinates r q.val, (mem_potentialCoordinateLocus_iff r q.val).mpr q.property⟩
  invFun f := ⟨potentialFromCoordinates r f.val,
    (mem_potentialCoordinateLocus_iff r _).mp (by simp only [potentialCoordinates_fromCoordinates]; exact f.property)⟩
  left_inv q := by apply Subtype.ext; exact potentialFromCoordinates_coordinates r q.val
  right_inv f := by apply Subtype.ext; exact potentialCoordinates_fromCoordinates r f.val

/-- The physical source locus is weak-star closed, including its period-one condition. -/
theorem isClosed_potentialCoordinateLocus (r : ℝ) : IsClosed (potentialCoordinateLocus r) := by
  have hc (n : ℤ) : Continuous (fun f => WeightedCoeff.weakStarCoordinates r f n) :=
    (continuous_apply n).comp (WeightedCoeff.continuous_weakStarCoordinates r)
  have ho : IsClosed {f | ∀ k : ℤ, WeightedCoeff.weakStarCoordinates r f (2*k+1) = 0} := by
    convert isClosed_iInter (fun k : ℤ => isClosed_eq (hc (2*k+1))
      (continuous_const : Continuous (fun _ : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) => (0:ℂ)))) using 1
    ext f
    simp
  exact (WeightedCoeff.isClosed_realMeanZeroWeakStar r).inter ho

/-- Compactness of norm balls for the exact physical source constraints. -/
theorem isCompact_potentialCoordinateBall (r R : ℝ) :
    IsCompact (WeightedCoeff.weakStarBall r R ∩ potentialCoordinateLocus r) :=
  (WeightedCoeff.isCompact_weakStarBall r R).inter_right (isClosed_potentialCoordinateLocus r)

/-- Metrizability with all three physical source restrictions retained. -/
theorem metrizable_potentialCoordinateBall (r R : ℝ) :
    TopologicalSpace.MetrizableSpace ↥(WeightedCoeff.weakStarBall r R ∩ potentialCoordinateLocus r) :=
  WeightedCoeff.metrizable_weakStar_compact r _ (isCompact_potentialCoordinateBall r R)

theorem isSeqCompact_potentialCoordinateBall (r R : ℝ) :
    IsSeqCompact (WeightedCoeff.weakStarBall r R ∩ potentialCoordinateLocus r) :=
  WeightedCoeff.isSeqCompact_of_isCompact_weakStar r (isCompact_potentialCoordinateBall r R)

/-- The source regularity interval admits the exact H-minus-one threshold. -/
theorem admissible_hminusOne_threshold (r : ℝ) (hr : AdmissiblePredualOrder r) :
    1 < ((-r)-(-1))*(2:ℝ≥0∞).toReal := by
  norm_num
  have hh := hr.2
  linarith

/-- The actual source potential as the identical original H-minus-one distribution. -/
def potentialHminusOne (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  PeriodicFourierLebesgue.endpointLowerInclusion (-r) (-1) (by norm_num)
    (admissible_hminusOne_threshold r hr) q.val

/-- No physical realization or normalization is changed by the H-minus-one inclusion. -/
theorem potentialHminusOne_val (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    (potentialHminusOne r hr q).val = q.val.val :=
  PeriodicFourierLebesgue.endpointLowerInclusion_val (-r) (-1) (by norm_num)
    (admissible_hminusOne_threshold r hr) q.val

/-- Reality, zero mean and physical period one survive in the H-minus-one domain. -/
theorem potentialHminusOne_source_conditions (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) : (potentialHminusOne r hr q).val.IsRealMeanZeroPeriodOne := by
  rw [potentialHminusOne_val]
  exact q.property

end NLS.Articles.KdVPseudomeasures
