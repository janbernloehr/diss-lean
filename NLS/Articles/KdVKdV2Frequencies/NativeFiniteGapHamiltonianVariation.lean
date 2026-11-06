import NLS.Articles.KdVKdV2Frequencies.NativeSourceFiniteActionVariation
import NLS.KdV.NativeHillPhysicalSource
import NLS.KdV.HillHminusActionAmplitudeDifferentials

/-! # Actual finite-gap physical Hamiltonian first variations

Native source actions are the original real Hill gap integrals, with exact
period and Abelian normalization. Thus the finite frequency expansion holds
under the actual spectral finite-gap hypothesis, without assuming an action
or Hamiltonian-frequency identification.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

private theorem physical_signed_product_eq_gap_integral (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) (n : ℤ)*
      hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) (-(n : ℤ)) =
      (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ) := by
  have he := hillPhysicalAbelianMap_action SpectralWeight.one (hillUnitRealSourceUnembed p) n n.pos
  have hp := congrArg (fun q : RealPeriodOneHillPotential =>
    hillRealGapIntegral q.val q.property.1 q.property.2 n 0) (hillRealWeightedEmbedding_unitUnembed p)
  change hillPeriodOneAction SpectralWeight.one (hillUnitRealSourceUnembed p).val
    (hillUnitRealSourceUnembed p).property n = hillRealGapIntegral p.val p.property.1 p.property.2 n 0 at hp
  simpa only [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply,hp] using! he

namespace GlobalRoughAbelianForwardData

/-- Every native source action is the ACTUAL original Hill gap integral,
on the entire real mean-zero H^m source and at every positive index. -/
theorem nativeSourceActionSequence_eq_gap_integral (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    (D.nativeSourceActionSequence m r hrs q).val (n : ℤ) =
      (hillRealGapIntegral (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n 0 : ℂ) := by
  rw [D.nativeSourceActionSequence_apply,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),
    nativeHillSource_eq_physical m q.val q.property.1,D.signed_physical,D.signed_physical]
  exact physical_signed_product_eq_gap_integral _ n

/-- Closed original spectral gaps are exactly the zero original source actions. -/
theorem nativeSourceActionSequence_zero_iff_closed_gap (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    (D.nativeSourceActionSequence m r hrs q).val (n : ℤ) = 0 ↔
      hillRealGapHalfLength (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0 := by
  let p := nativeHillPhysicalSource m q.val q.property.1
  rw [D.nativeSourceActionSequence_eq_gap_integral]
  constructor
  · intro h
    have hr : hillRealGapIntegral p.val p.property.1 p.property.2 n 0 = 0 := by exact_mod_cast h
    by_contra hopen
    have hpos := hillRealGapIntegral_pos_of_open p n hopen
    linarith
  · intro hgap
    have he : hillRealLabels p.val p.property.1 p.property.2 (2*n-1) =
        hillRealLabels p.val p.property.1 p.property.2 (2*n) := by
      change (hillRealLabels p.val p.property.1 p.property.2 (2*n)-
        hillRealLabels p.val p.property.1 p.property.2 (2*n-1))/2=0 at hgap
      linarith
    rw [hillRealGapIntegral_closed p.val p.property.1 p.property.2 n 0 he,Complex.ofReal_zero]

/-- The true spectral finite-gap condition is equivalent to finite support
of the complete original action sequence, with the same positive indices. -/
theorem nativeSourceActionSequence_finite_support_iff (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+) :
    (∀ n : ℕ+, n ∉ S → (D.nativeSourceActionSequence m r hrs q).val (n : ℤ) = 0) ↔
      ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
        (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0 := by
  constructor
  · intro h n hn
    exact (D.nativeSourceActionSequence_zero_iff_closed_gap m r hrs q n).mp (h n hn)
  · intro h n hn
    exact (D.nativeSourceActionSequence_zero_iff_closed_gap m r hrs q n).mpr (h n hn)

/-- The actual physical H_m finite-gap first variation, with every native
source variation and the original Hill spectral condition. -/
theorem nativeSourceHierarchyHamiltonian_fderiv_finite_gap
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    (fderiv ℝ (D.nativeSourceHierarchyHamiltonian m) q) h = ∑ n ∈ S,
      ((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val (n : ℤ)*
        (D.originalHierarchyFrequency m r hrs
          (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)) n : ℂ) :=
  D.nativeSourceHierarchyHamiltonian_fderiv_finite_actions m r hrs q S
    ((D.nativeSourceActionSequence_finite_support_iff m r hrs q S).mpr hq) h

/-- The exact printed physical KdV Hamiltonian at ANY actual native finite-gap source. -/
theorem nativeKdVHamiltonian_fderiv_finite_gap (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    (fderiv ℝ (fun u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) => nativeKdVHamiltonian u.val) q) h =
      ∑ n ∈ S, ((fderiv ℝ (D.nativeSourceActionSequence 1 3 (by norm_num)) q) h).val (n : ℤ)*
        (D.originalKdVFrequency (originalPositiveActions 1 3 (by norm_num) (D.rawIntegerForwardHomeomorph 1 q)) n : ℂ) :=
  D.nativeKdVHamiltonian_fderiv_finite_actions q S
    ((D.nativeSourceActionSequence_finite_support_iff 1 3 (by norm_num) q S).mpr hq) h

/-- The exact printed physical KdV2 Hamiltonian with the SAME finite-gap spectral meaning. -/
theorem nativeKdV2Hamiltonian_fderiv_finite_gap (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) :
    (fderiv ℝ (fun u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ)) => nativeKdV2Hamiltonian u.val) q) h =
      ∑ n ∈ S, ((fderiv ℝ (D.nativeSourceActionSequence 2 5 (by norm_num)) q) h).val (n : ℤ)*
        (D.originalKdV2Frequency (originalPositiveActions 2 5 (by norm_num) (D.rawIntegerForwardHomeomorph 2 q)) n : ℂ) :=
  D.nativeKdV2Hamiltonian_fderiv_finite_actions q S
    ((D.nativeSourceActionSequence_finite_support_iff 2 5 (by norm_num) q S).mpr hq) h

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
