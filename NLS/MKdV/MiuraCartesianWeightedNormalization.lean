import NLS.MKdV.MiuraPositiveCartesianMap
import NLS.ZakharovShabat.SourceDiagonalActionRootSequenceCompact
import NLS.SequenceSpaces.AnalyticPhaseTrajectory

/-! # Weight normalization of the actual Cartesian map

The native half-order target embeds by its weight into an ordinary
coefficient pair and the mean. A bounded left inverse recovers the full
positive target. Locally the normalized map is exactly multiplication of
the original NLS coordinates by the analytic scaled-root sequence.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraNormalizedCartesianTarget := (Coeff 2 × Coeff 2) × ℂ

def miuraCartesianWeightEmbedding : MiuraPositiveHalf →L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (1/2)) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    MiuraPositiveHalf.subtypeL

def miuraCartesianWeightRetraction : Coeff 2 →L[ℂ] MiuraPositiveHalf :=
  (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2).comp
    (WeightedCoeff.weightIsometry (Weight.sobolev (1/2)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem miuraCartesianWeightRetraction_embedding (z : MiuraPositiveHalf) :
    miuraCartesianWeightRetraction (miuraCartesianWeightEmbedding z) = z := by
  change WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2
    ((WeightedCoeff.weightIsometry (Weight.sobolev (1/2)) 2).symm
      ((WeightedCoeff.weightIsometry (Weight.sobolev (1/2)) 2) z.val)) = z
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact WeightedCoeff.positiveProjection_eq_self _ _ z

def miuraCartesianNormalization : MiuraPositiveCartesianTarget →L[ℂ] MiuraNormalizedCartesianTarget :=
  (miuraCartesianWeightEmbedding.prodMap miuraCartesianWeightEmbedding).prodMap
    (ContinuousLinearMap.id ℂ ℂ)

def miuraCartesianDenormalization : MiuraNormalizedCartesianTarget →L[ℂ] MiuraPositiveCartesianTarget :=
  (miuraCartesianWeightRetraction.prodMap miuraCartesianWeightRetraction).prodMap
    (ContinuousLinearMap.id ℂ ℂ)

theorem miuraCartesianDenormalization_normalization (z : MiuraPositiveCartesianTarget) :
    miuraCartesianDenormalization (miuraCartesianNormalization z) = z :=
  Prod.ext (Prod.ext (miuraCartesianWeightRetraction_embedding z.1.1)
    (miuraCartesianWeightRetraction_embedding z.1.2)) rfl

def miuraNLSCoordinateSequence (a : Coeff 2) : Coeff 2 × Coeff 2 :=
  sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal a)

def miuraCartesianRootSequence (a : Coeff 2) : Coeff ⊤ :=
  sourceDiagonalActionRootSequence (scalarL2Diagonal a)

def miuraScaledNLSCartesianMap (a : Coeff 2) : MiuraNormalizedCartesianTarget :=
  ((Coeff.multiplier (miuraCartesianRootSequence a) (miuraNLSCoordinateSequence a).1,
    -(Coeff.multiplier (miuraCartesianRootSequence a) (miuraNLSCoordinateSequence a).2)),a 0)

theorem miuraCartesianNormalization_map_eventually (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    (fun b => miuraCartesianNormalization (miuraPositiveCartesianMap b)) =ᶠ[𝓝 a]
      miuraScaledNLSCartesianMap := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a,scalarL2Diagonal_realDiagonal a ha⟩
  obtain ⟨U,hU,haU,_,hcoord⟩ := exists_local_miuraL2CartesianSequence_analytic a ha
  obtain ⟨V,hV,hφV,_,hroot⟩ := exists_local_sourceDiagonalActionRootSequence_analytic φ
  have haV : a ∈ scalarL2Diagonal ⁻¹' V := hφV
  filter_upwards [hU.mem_nhds haU,(hV.preimage scalarL2Diagonal.continuous).mem_nhds haV] with b hbU hbV
  have he (n : ℤ) := hroot (scalarL2Diagonal b) hbV n
  apply Prod.ext
  · apply Prod.ext
    · ext n
      change (Weight.sobolev (1/2) n : ℂ)*
        (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence b).1).val.val n =
          sourceDiagonalActionRootSequence (scalarL2Diagonal b) n*(miuraNLSCoordinateSequence b).1 n
      rw [WeightedCoeff.positiveProjection_apply,he,sourceDiagonalScaledActionRoot]
      by_cases hn : 0 < n
      · have hx := congrArg Prod.fst (hcoord b hbU n)
        change (miuraL2CartesianSequence b).1.val n = _ at hx
        rw [if_pos hn,if_pos hn,hx]
        simp only [miuraL2CartesianCoefficient,if_pos hn,miuraL2CartesianCoordinates,
          Int.toNat_of_nonneg hn.le,miuraNLSCoordinateSequence]
        ring
      · simp only [if_neg hn,mul_zero,zero_mul]
    · ext n
      change (Weight.sobolev (1/2) n : ℂ)*
        (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence b).2).val.val n =
          -(sourceDiagonalActionRootSequence (scalarL2Diagonal b) n*(miuraNLSCoordinateSequence b).2 n)
      rw [WeightedCoeff.positiveProjection_apply,he,sourceDiagonalScaledActionRoot]
      by_cases hn : 0 < n
      · have hy := congrArg Prod.snd (hcoord b hbU n)
        change (miuraL2CartesianSequence b).2.val n = _ at hy
        rw [if_pos hn,if_pos hn,hy]
        simp only [miuraL2CartesianCoefficient,if_pos hn,miuraL2CartesianCoordinates,
          Int.toNat_of_nonneg hn.le,miuraNLSCoordinateSequence]
        ring
      · simp only [if_neg hn,mul_zero,zero_mul,neg_zero]
  · rfl

end NLS.MKdV
