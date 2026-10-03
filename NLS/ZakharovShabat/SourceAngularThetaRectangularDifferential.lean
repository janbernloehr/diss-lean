import NLS.ZakharovShabat.SourceBirkhoffOpenGapPoisson
import NLS.ZakharovShabat.SourceBirkhoffLemma15_3

/-! # The angle differential in actual rectangular coordinates

On the selected open gap, the actual angle cotangent is
`(-y dx + x dy)/(2 I)`. Compatibility of normalized families transfers
this identity to the coordinates of any constructed Birkhoff map.
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}

namespace SourceAngularThetaCommonDomainData
variable {V₀ C V : Set (CoeffPair p)} {t : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The branch-independent theta cotangent is the polar angle differential. -/
theorem thetaDifferential_eq_rectangular
    (E : SourceAngularThetaCommonDomainData hp hp1 V₀ C V t)
    (k : ℤ) (φ : realTypeSourceSubmodule p)
    (hk : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    sourceAngularThetaDifferential hp hp1 k t φ.val =
      (-sourceBirkhoffY hp hp1 k t φ.val / (2*sourceComplexAction hp hp1 k φ.val)) •
        fderiv ℂ (sourceBirkhoffX hp hp1 k t) φ.val +
      (sourceBirkhoffX hp hp1 k t φ.val / (2*sourceComplexAction hp hp1 k φ.val)) •
        fderiv ℂ (sourceBirkhoffY hp hp1 k t) φ.val := by
  have hd := E.birkhoffXY_fderiv k φ hk
  have hrad := E.birkhoffXY_action_radius k φ hk
  have hne := birkhoff_action_ne_zero k φ hk
  rw [hd.1,hd.2]
  ext h
  simp only [add_apply,smul_apply,smul_eq_mul]
  field_simp
  linear_combination -2*sourceComplexAction hp hp1 k φ.val*
    (sourceAngularThetaDifferential hp hp1 k t φ.val h)*hrad

end SourceAngularThetaCommonDomainData

namespace SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair p)}
  {s t : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The angle family need not be the family used to construct the map. -/
theorem thetaDifferential_eq_map_rectangular
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hp hp1 V₀ C V t)
    (k : ℤ) (φ : realTypeSourceSubmodule p)
    (hk : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    sourceAngularThetaDifferential hp hp1 k t φ.val =
      (-(sourceBirkhoffMap hp hp1 s φ.val).2 k / (2*sourceComplexAction hp hp1 k φ.val)) •
        fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 k) φ.val +
      ((sourceBirkhoffMap hp hp1 s φ.val).1 k / (2*sourceComplexAction hp hp1 k φ.val)) •
        fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 k) φ.val := by
  have hi : CoeffPair.exponentInclusion (le_refl p) = ContinuousLinearMap.id ℂ (CoeffPair p) := by
    apply ContinuousLinearMap.ext
    intro u
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n <;> rfl
  have hv := D.angular.birkhoffXY_real_exponent E.toSourceAngularEtaLocalCommonDomainData
    W V D.source_open E.source_open D.source_subset E.source_subset (le_refl p) k φ
    (D.real_subset φ.property) (by simpa only [hi,ContinuousLinearMap.id_apply] using E.real_subset φ.property)
  have hd := D.angular.fderiv_birkhoffXY_exponent E.toSourceAngularEtaLocalCommonDomainData
    W V D.source_open E.source_open D.source_subset E.source_subset D.real_subset E.real_subset (le_refl p) k φ
  simp only [hi,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_id] at hv hd
  rw [E.thetaDifferential_eq_rectangular k φ hk,← hv.1,← hv.2,← hd.1,← hd.2]
  rw [(D.coordinates φ.val (D.real_subset φ.property) k).1,
    (D.coordinates φ.val (D.real_subset φ.property) k).2,
    (D.fderiv_coordinates k φ.val (D.real_subset φ.property)).1,
    (D.fderiv_coordinates k φ.val (D.real_subset φ.property)).2]

/-- Both rectangular derivatives along the actual theta Hamiltonian,
including every unselected collapsed gap. -/
theorem map_coordinates_thetaHamiltonian
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hp hp1 V₀ C V t)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k n : ℤ) (φ : realTypeSourceSubmodule p)
    (hk : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    let v := sourceHamiltonianDirection h2p (sourceAngularThetaDifferential hp hp1 k t φ.val)
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val) v =
      -((sourceBirkhoffMap hp hp1 s φ.val).1 k / (2*sourceComplexAction hp hp1 k φ.val)) *
        (if n = k then 1 else 0) ∧
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val) v =
      -((sourceBirkhoffMap hp hp1 s φ.val).2 k / (2*sourceComplexAction hp hp1 k φ.val)) *
        (if n = k then 1 else 0) := by
  dsimp only
  rw [apply_sourceHamiltonianDirection,apply_sourceHamiltonianDirection,
    D.thetaDifferential_eq_map_rectangular E k φ hk]
  have hnk := D.sourceBracket_canonical h2p n k φ
  have hkn := D.sourceBracket_canonical h2p k n φ
  change sourceBivector h2p _ _ = 0 ∧ sourceBivector h2p _ _ = _ ∧ sourceBivector h2p _ _ = 0 at hnk hkn
  have hrev : sourceBivector h2p
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val)
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 k) φ.val) = (if n = k then 1 else 0) := by
    rw [sourceBivector_antisymm,hkn.2.1]
    simp only [neg_neg,eq_comm]
  simp only [map_add,map_smul,smul_eq_mul,hnk.1,hnk.2.1,hnk.2.2,hrev]
  constructor <;> ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
