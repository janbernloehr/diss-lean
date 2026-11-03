import NLS.MKdV.MiuraActionFieldTrace
import NLS.MKdV.MiuraCartesianGardnerAction

/-! # The physical spatial generator on every Cartesian pair

The convergent Gardner action-field trace and the actual mixed brackets
give the spatial derivative identity, including a collapsed selected gap.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianSpatialGenerator (m : ℕ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (2*(Real.pi : ℂ)*m) •
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod (-(ContinuousLinearMap.fst ℂ ℂ ℂ)))

theorem fderiv_miuraCartesian_spatialDerivative (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    (fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a)) (periodOneDerivative a) =
      miuraCartesianSpatialGenerator m (miuraL2CartesianCoordinates m (scalarInclusion a)) := by
  let L := fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a)
  have ht := L.hasSum (hasSum_miuraGardnerDirections_spatialDerivative a ha)
  have he : (fun k : ℕ => L ((2*(Real.pi : ℂ)*(k+1)) •
      l2GardnerDirection (miuraL2Action (k+1)) (scalarInclusion a))) =
      (fun k : ℕ => if k = m-1 then miuraCartesianSpatialGenerator m
        (miuraL2CartesianCoordinates m (scalarInclusion a)) else 0) := by
    funext k
    rw [map_smul]
    change (2*(Real.pi : ℂ)*(k+1)) •
      ((fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a))
        (l2GardnerDirection (miuraL2Action (k+1)) (scalarInclusion a))) = _
    rw [fderiv_miuraCartesian_apply_Gardner_action a ha m (k+1) hm (by omega)]
    by_cases hk : k = m-1
    · have hmk : m = k+1 := by omega
      rw [if_pos hk,if_pos hmk,hmk]
      simp [miuraCartesianSpatialGenerator]
    · have hmk : m ≠ k+1 := by omega
      rw [if_neg hk,if_neg hmk,smul_zero]
  rw [he] at ht
  exact ht.unique (hasSum_ite_eq (m-1) _)

end NLS.MKdV
