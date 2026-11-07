import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSignedGardner
import NLS.KdV.HillNativeSelectedPhaseCotangent
import NLS.KdV.HillCompletePhaseHamiltonianVector

/-! The genuine complete-phase Hamiltonian vector changes only the
selected native coordinate pair. This includes all other collapsed
modes, where zero action velocity alone would not determine a tangent. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson
namespace NLS.Articles.KdVPseudomeasures

theorem hillRealNativeCoordinate_completePhase_Gardner
    {P : HillProductEquationPatch} {n : ℕ+} (A : HillPhysicalOnIndexPhaseChart P n)
    (q : HillRealMeanZeroSource) (hq : hillRealMeanZeroInclusion q ∈ A.source) (k : ℤ) :
    hminusGardnerBracket (hillHminusNativeCoordinate k) A.completePhase (hillRealMeanZeroInclusion q)=
      if k=(n:ℤ) then (2*hillHminusNativeCoordinate (-(n:ℤ)) (hillRealMeanZeroInclusion q))⁻¹
      else if k=-(n:ℤ) then (2*hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q))⁻¹ else 0 := by
  let Q := hillRealMeanZeroInclusion q
  have hr : IsRealPeriodOneHminusOne Q := q.property
  have hn : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  have hn0 : (n:ℤ)≠0 := ne_of_gt hn
  have hnneg : (n:ℤ)≠-(n:ℤ) := by omega
  have hp := hillRealNativeGardner_signed_canonical (n:ℤ) k q
  rw [if_neg hn0,if_pos hn] at hp
  have hm := hillRealNativeGardner_signed_canonical (-(n:ℤ)) k q
  rw [if_neg (by omega : -(n:ℤ)≠0),neg_neg,if_neg (by omega : ¬ (0:ℤ) < -(n:ℤ))] at hm
  have hkp : gardnerCotangentBivector (fderiv ℂ (hillHminusNativeCoordinate k) Q)
      (fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) Q)= -(if k=-(n:ℤ) then I else 0) := by
    change hillHminusNativeGardnerBracket k (n:ℤ) Q=_
    rw [hillHminusNativeGardnerBracket_antisymm,hp]
  have hkm : gardnerCotangentBivector (fderiv ℂ (hillHminusNativeCoordinate k) Q)
      (fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) Q)= -(if k=(n:ℤ) then -I else 0) := by
    change hillHminusNativeGardnerBracket k (-(n:ℤ)) Q=_
    rw [hillHminusNativeGardnerBracket_antisymm,hm]
  change gardnerCotangentBivector (fderiv ℂ (hillHminusNativeCoordinate k) Q)
    (fderiv ℂ A.completePhase Q)=_
  rw [A.completePhase_fderiv_eq_selected_pair Q hq hr]
  simp only [map_smul,map_sub,smul_eq_mul]
  rw [hkp,hkm]
  by_cases hk : k=(n:ℤ)
  · subst k
    simp [hnneg,div_eq_mul_inv]
    ring_nf
    simp [I_sq]
    ring
  · by_cases hkmn : k=-(n:ℤ)
    · subst k
      simp [Ne.symm hnneg,div_eq_mul_inv]
      ring_nf
      simp [I_sq]
      ring
    · simp only [if_neg hk,if_neg hkmn,neg_zero,mul_zero,sub_zero]

theorem hillRealNativeCoordinate_phase_Hamiltonian_velocity
    {P : HillProductEquationPatch} {n : ℕ+} (A : HillPhysicalOnIndexPhaseChart P n)
    (q : HillRealMeanZeroSource) (hq : hillRealMeanZeroInclusion q ∈ A.source) (k : ℤ) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion q))
      (gardnerHamiltonianVector A.completePhase (hillRealMeanZeroInclusion q))=
      if k=(n:ℤ) then (2*hillHminusNativeCoordinate (-(n:ℤ)) (hillRealMeanZeroInclusion q))⁻¹
      else if k=-(n:ℤ) then (2*hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q))⁻¹ else 0 := by
  rw [fderiv_apply_gardnerHamiltonianVector]
  exact hillRealNativeCoordinate_completePhase_Gardner A q hq k

end NLS.Articles.KdVPseudomeasures
