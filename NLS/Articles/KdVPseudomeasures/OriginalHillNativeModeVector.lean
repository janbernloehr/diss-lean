import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSignedGardner
import NLS.Articles.KdVPseudomeasures.OriginalHillH1ModeCurve
import NLS.Poisson.GardnerHamiltonianZeroMode

/-! Real native-coordinate Hamiltonian directions at EVERY mode, with
no open-gap condition. The two signed canonical brackets determine every
coordinate velocity of their physical real linear combinations. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillNativeModeHamiltonianVector (n : ℕ+) (c : ℂ) (q : PeriodOneHminusOne) : PeriodOneHminusOne :=
  (-I*c) • gardnerHamiltonianVector (hillHminusNativeCoordinate (-(n:ℤ))) q+
    (I*(starRingEnd ℂ) c) • gardnerHamiltonianVector (hillHminusNativeCoordinate (n:ℤ)) q

theorem hillNativeModeHamiltonianVector_zero_mode (n : ℕ+) (c : ℂ) (q : PeriodOneHminusOne) :
    (hillNativeModeHamiltonianVector n c q).val 0=0 := by
  change (-I*c)*(gardnerHamiltonianDirection (fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) q)).val 0+
    (I*(starRingEnd ℂ) c)*(gardnerHamiltonianDirection (fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) q)).val 0=0
  rw [gardnerHamiltonianDirection_zero_mode,gardnerHamiltonianDirection_zero_mode]
  ring

theorem hillNativeModeHamiltonianVector_native_velocity (n : ℕ+) (c : ℂ)
    (q : HillRealMeanZeroSource) (k : ℤ) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion q))
      (hillNativeModeHamiltonianVector n c (hillRealMeanZeroInclusion q))=
        (hillH1ModeCLM n c).val.val.val k := by
  let Q := hillRealMeanZeroInclusion q
  have hn : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  have hp := hillRealNativeGardner_signed_canonical (n:ℤ) k q
  rw [if_neg (ne_of_gt hn),if_pos hn] at hp
  have hm := hillRealNativeGardner_signed_canonical (-(n:ℤ)) k q
  rw [if_neg (by omega : -(n:ℤ)≠0),neg_neg,if_neg (by omega : ¬(0:ℤ)< -(n:ℤ))] at hm
  have hkp : hminusGardnerBracket (hillHminusNativeCoordinate k) (hillHminusNativeCoordinate (n:ℤ)) Q=
      -(if k=-(n:ℤ) then I else 0) := by
    change hillHminusNativeGardnerBracket k (n:ℤ) Q=_
    rw [hillHminusNativeGardnerBracket_antisymm,hp]
  have hkm : hminusGardnerBracket (hillHminusNativeCoordinate k) (hillHminusNativeCoordinate (-(n:ℤ))) Q=
      -(if k=(n:ℤ) then -I else 0) := by
    change hillHminusNativeGardnerBracket k (-(n:ℤ)) Q=_
    rw [hillHminusNativeGardnerBracket_antisymm,hm]
  rw [hillNativeModeHamiltonianVector,map_add,map_smul,map_smul,
    fderiv_apply_gardnerHamiltonianVector,fderiv_apply_gardnerHamiltonianVector,hkp,hkm,hillH1ModeCLM_apply]
  simp only [smul_eq_mul]
  by_cases hk : k=(n:ℤ)
  · subst k
    simp [show (n:ℤ)≠-(n:ℤ) by omega]; ring_nf; simp
  · by_cases hm : k=-(n:ℤ)
    · subst k
      simp [hk]; ring_nf; simp
    · simp [hk,hm]

end NLS.Articles.KdVPseudomeasures
