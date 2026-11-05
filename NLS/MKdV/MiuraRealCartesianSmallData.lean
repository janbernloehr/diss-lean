import NLS.MKdV.MiuraRealCartesianLocalInverse
import NLS.FunctionalAnalysis.ProperMapLocalUniqueness

/-! # Globally unique physical preimages for small real Cartesian data

The zero fiber is a singleton by the actual mass/action trace. Properness
excludes distant extra preimages near that fiber. Combined with the actual
real inverse chart, this gives existence and global uniqueness for every
point of a full real target neighborhood, including closed actions.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPhysicalCartesianMap_eq_zero_iff (a : Coeff.physicalRealSubmodule 2) :
    miuraPhysicalCartesianMap a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have he := congrArg (fun z : MiuraRealCartesianTarget => miuraPositiveCartesianInclusion z.val) ha
    rw [miuraPhysicalCartesianMap_inclusion,miuraPositiveCartesianInclusion_map a.val a.property] at he
    change miuraL2CartesianMeanMap a.val = 0 at he
    have hs := congrArg Prod.fst he
    have hm := congrArg Prod.snd he
    change miuraL2CartesianSequence a.val = 0 at hs
    change a.val 0 = 0 at hm
    have hJ : miuraL2ActionSequence a.val = 0 := by
      rw [← miuraL2CartesianActions_sequence_eq a.val a.property,hs]
      apply Subtype.ext
      funext n
      rw [miuraL2CartesianActions_apply]
      change (1/2 : ℂ)*(0^2+0^2) = 0
      norm_num
    have hM : miuraL2ActionMoment a.val = 0 := by
      change miuraL2ActionMomentFunctional (miuraL2ActionSequence a.val) = 0
      rw [hJ,map_zero]
    have hn := miuraL2_norm_sq_eq_action_mean a.val a.property
    rw [hm,hM] at hn
    have hn0 : ‖a.val‖ = 0 := by
      simp only [Complex.zero_re,zero_pow (by omega : (2 : ℕ) ≠ 0),mul_zero,add_zero] at hn
      nlinarith [norm_nonneg a.val]
    apply Subtype.ext
    exact norm_eq_zero.mp hn0
  · rintro rfl
    exact miuraPhysicalCartesianMap_zero

/-- Every sufficiently small real native Cartesian pair and real signed
mean has exactly one preimage in the entire physical real L² space. -/
theorem exists_miuraPhysicalCartesian_global_unique_small_data :
    ∃ V : Set MiuraRealCartesianTarget, IsOpen V ∧ (0 : MiuraRealCartesianTarget) ∈ V ∧
      ∀ z ∈ V, ∃! a : Coeff.physicalRealSubmodule 2, miuraPhysicalCartesianMap a = z := by
  obtain ⟨U,V,hU,hV,h0U,h0V,_,hbij,G,_,_,_,_,hG⟩ :=
    exists_miuraPhysicalCartesian_localInverse_at_zero
  obtain ⟨W,hW,h0W,_,_,huniq⟩ :=
    NLS.FunctionalAnalysis.exists_open_global_unique_preimages_of_proper_local_chart
      isProperMap_miuraPhysicalCartesianMap (0 : Coeff.physicalRealSubmodule 2)
      (fun b hb => (miuraPhysicalCartesianMap_eq_zero_iff b).mp (hb.trans miuraPhysicalCartesianMap_zero))
      hU h0U hV (miuraPhysicalCartesianMap_zero.symm ▸ h0V) hbij.2.1
      (fun z hz => ⟨G z,(hG z hz).1,(hG z hz).2⟩)
  exact ⟨W,hW,miuraPhysicalCartesianMap_zero ▸ h0W,huniq⟩

end NLS.MKdV
