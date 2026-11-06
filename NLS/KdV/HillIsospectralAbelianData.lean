import NLS.KdV.HillComplexHilbertNormalizedUniqueness
import NLS.KdV.HillRegularAngleCompatibility

/-! # Independent Abelian data depend only on the original periodic labels

The normalized numerator is compared by its proved period uniqueness.
No invariance of an arbitrary choice of global numerator roots is assumed.
The canonical and deflated roots, cosine differential and its primitive
then retain their literal original normalizations on each isospectral set.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

variable (q r : RealPeriodOneHillPotential)
    (hl : hillRealLabels q.val q.property.1 q.property.2 =
      hillRealLabels r.val r.property.1 r.property.2)

include hl

theorem hillGapRootBox_eq_of_labels :
    hillGapRootBox q.val q.property.1 q.property.2 = hillGapRootBox r.val r.property.1 r.property.2 := by
  simp only [hillGapRootBox,hl]

theorem hillRealGapCenter_eq_of_labels :
    hillRealGapCenter q.val q.property.1 q.property.2 = hillRealGapCenter r.val r.property.1 r.property.2 := by
  funext k
  simp only [hillRealGapCenter,hl]

theorem hillRealGapHalfLength_eq_of_labels :
    hillRealGapHalfLength q.val q.property.1 q.property.2 = hillRealGapHalfLength r.val r.property.1 r.property.2 := by
  funext k
  simp only [hillRealGapHalfLength,hl]

theorem hillRealGapCollar_eq_of_labels :
    hillRealGapCollar q.val q.property.1 q.property.2 = hillRealGapCollar r.val r.property.1 r.property.2 := by
  funext k
  simp only [hillRealGapCollar,hl]

theorem hillEnergyCanonicalRootProduct_eq_of_labels :
    hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 =
      hillEnergyCanonicalRootProduct r.val r.property.1 r.property.2 := by
  funext E
  simp only [hillEnergyCanonicalRootProduct,hillEnergyRootProduct,hillEnergyRootFactor,hl]

theorem hillDeflatedEnergyCanonicalRoot_eq_of_labels (k : ℕ) :
    hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k =
      hillDeflatedEnergyCanonicalRoot r.val r.property.1 r.property.2 k := by
  funext E
  simp only [hillDeflatedEnergyCanonicalRoot,hillOmittedEnergyRootProduct,
    hillOmittedEnergyRootFactor,hillEnergyRootFactor,hl]

theorem hillAbelianCandidatePeriod_eq_of_labels (σ : ℕ → ℝ) (n k : ℕ) :
    hillAbelianCandidatePeriod q.val q.property.1 q.property.2 σ n k =
      hillAbelianCandidatePeriod r.val r.property.1 r.property.2 σ n k := by
  unfold hillAbelianCandidatePeriod
  rw [hillRealGapCenter_eq_of_labels q r hl,hillRealGapHalfLength_eq_of_labels q r hl,
    hillRealGapCollar_eq_of_labels q r hl,hillEnergyCanonicalRootProduct_eq_of_labels q r hl]

theorem hillAbelianSelectedGlobalPsi_eq_of_labels (n : ℕ) (hn : 1 ≤ n) :
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn =
      hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn := by
  let σ := (hillAbelianSelectedGlobalRoots r.val r.property.1 r.property.2 n hn).val
  have hσr : σ ∈ hillGapRootBox r.val r.property.1 r.property.2 :=
    (hillAbelianSelectedGlobalRoots r.val r.property.1 r.property.2 n hn).property
  have hσq : σ ∈ hillGapRootBox q.val q.property.1 q.property.2 := by
    rwa [hillGapRootBox_eq_of_labels q r hl]
  let a := hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 σ hσq
  have hp (k : ℕ) : hillAbelianHilbertPeriod q.val q.property.1 q.property.2 n k a =
      hillAbelianCandidatePeriod r.val r.property.1 r.property.2 σ n k :=
    (hillAbelianHilbertPeriod_eq_genuine_period q.val q.property.1 q.property.2 σ hσq n k).trans
      (hillAbelianCandidatePeriod_eq_of_labels q r hl σ n k)
  have hown : hillAbelianHilbertPeriod q.val q.property.1 q.property.2 n n a ≠ 0 := by
    rw [hp]
    exact (hillAbelianSelectedGlobalRoots_periods r.val r.property.1 r.property.2 n hn).1
  have hzero (k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n) :
      hillAbelianHilbertPeriod q.val q.property.1 q.property.2 n k a = 0 := by
    rw [hp]
    have h := (hillAbelianSelectedGlobalRoots_periods r.val r.property.1 r.property.2 n hn).2 k hk
    rw [if_neg hkn,div_eq_zero_iff] at h
    exact h.resolve_right (hillAbelianSelectedGlobalRoots_periods r.val r.property.1 r.property.2 n hn).1
  have he := hillAbelian_complex_normalized_hilbertPsi_eq_selected q.val q.property.1 q.property.2
    (by simp) (by simp [IsRealHillPotential]) n hn a hown hzero
  funext E
  rw [← congrFun he E]
  rw [hillAbelianHilbertPsi_eq_genuine_candidate q.val q.property.1 q.property.2 σ hσq n E,hp n]
  rfl

theorem hillAbelianCosineDifferential_eq_of_labels (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn k =
      hillAbelianCosineDifferential r.val r.property.1 r.property.2 n hn k := by
  funext θ
  unfold hillAbelianCosineDifferential
  rw [hillAbelianSelectedGlobalPsi_eq_of_labels q r hl n hn,
    hillDeflatedEnergyCanonicalRoot_eq_of_labels q r hl k,hillRealGapCenter_eq_of_labels q r hl,
    hillRealGapHalfLength_eq_of_labels q r hl]

theorem hillAbelianCosinePrimitive_eq_of_labels (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn k =
      hillAbelianCosinePrimitive r.val r.property.1 r.property.2 n hn k := by
  funext θ
  simp only [hillAbelianCosinePrimitive,hillAbelianCosineDifferential_eq_of_labels q r hl n hn k]

theorem hillRegularAbelianPrimitive_eq_of_labels (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    hillRegularAbelianPrimitive q.val q.property.1 q.property.2 n hn k =
      hillRegularAbelianPrimitive r.val r.property.1 r.property.2 n hn k := by
  funext θ
  simp only [hillRegularAbelianPrimitive,hillAbelianCosinePrimitive_eq_of_labels q r hl n hn k]

end NLS.KdV
