import NLS.KdV.HillBirkhoffTargetSpaces
import NLS.KdV.HillOriginalRealCartesianGardner

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The fixed ORIGINAL real Birkhoff map: decode the globally invertible
literal physical spectral sequence into the exact real weighted target. -/
def hillOriginalBirkhoffMap (q : hillRealMeanZeroSourceSubmodule) : HillBirkhoffSpace :=
  (RealWeightedNatPair.normalizationEquiv _ _).symm (hillOriginalMeanZeroRealSpectralMap q)

/-- The actual map's raw coordinates are the SAME original full spectral
coordinates with fixed canonical orientation, at EVERY source and index. -/
theorem hillOriginalBirkhoffMap_coordinates (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    (hillOriginalBirkhoffMap q).val k =
      (hillOriginalBirkhoffX q ⟨k+1,by omega⟩,hillOriginalBirkhoffY q ⟨k+1,by omega⟩) := by
  apply RealWeightedNatPair.normalization_symm_apply_of_mul
  change hillOriginalMeanZeroRealSpectralMap q k = (hillBirkhoffBaseWeight k : ℂ)*
    hillSpectralCartesian q.val.val q.val.property.1 q.val.property.2 (k+1) (by omega)
  exact hillOriginalBaseSpectralSequence_apply ⟨q.val.val,q.val.property⟩ k

/-- The fixed ORIGINAL real map as an actual global homeomorphism,
with the paper's real weighted target norm, not an abstract norm witness. -/
def hillOriginalBirkhoffHomeomorph : hillRealMeanZeroSourceSubmodule ≃ₜ HillBirkhoffSpace :=
  hillOriginalMeanZeroSpectralHomeomorph.trans
    (RealWeightedNatPair.normalizationIsometry _ _).symm.toHomeomorph

@[simp] theorem hillOriginalBirkhoffHomeomorph_apply (q : hillRealMeanZeroSourceSubmodule) :
    hillOriginalBirkhoffHomeomorph q = hillOriginalBirkhoffMap q := rfl

def hillOriginalBirkhoffInverse : HillBirkhoffSpace → hillRealMeanZeroSourceSubmodule :=
  hillOriginalBirkhoffHomeomorph.symm

@[simp] theorem hillOriginalBirkhoffInverse_apply_map (q : hillRealMeanZeroSourceSubmodule) :
    hillOriginalBirkhoffInverse (hillOriginalBirkhoffMap q) = q :=
  hillOriginalBirkhoffHomeomorph.symm_apply_apply q

@[simp] theorem hillOriginalBirkhoffMap_apply_inverse (z : HillBirkhoffSpace) :
    hillOriginalBirkhoffMap (hillOriginalBirkhoffInverse z) = z :=
  hillOriginalBirkhoffHomeomorph.apply_symm_apply z

/-- Both directions of the SAME physical real Birkhoff map are real
Banach analytic in the ORIGINAL source and target Hilbert topologies. -/
theorem analyticOnNhd_hillOriginalBirkhoffMap : AnalyticOnNhd ℝ hillOriginalBirkhoffMap univ := by
  intro q _
  exact ((RealWeightedNatPair.normalizationIsometry _ _).symm.toContinuousLinearEquiv.analyticAt _).comp
    (analyticOnNhd_hillOriginalMeanZeroRealSpectralMap q (mem_univ _))

theorem analyticOnNhd_hillOriginalBirkhoffInverse : AnalyticOnNhd ℝ hillOriginalBirkhoffInverse univ := by
  intro z _
  exact (analyticOnNhd_hillOriginalMeanZeroSpectralInverse _ (mem_univ _)).comp
    ((RealWeightedNatPair.normalizationIsometry _ _).toContinuousLinearEquiv.analyticAt z)

/-- Exact Parseval identity for the literal real physical map. -/
theorem norm_hillOriginalBirkhoffMap (q : hillRealMeanZeroSourceSubmodule) :
    ‖hillOriginalBirkhoffMap q‖ = ‖q‖ := by
  exact (RealWeightedNatPair.normalizationIsometry _ _).symm.norm_map _ |>.trans
    (norm_hillOriginalMeanZeroRealSpectralMap q)

/-- Canonical original real coordinates have the original physical actions
at EVERY source, including every low and collapsed gap. -/
theorem hillOriginalBirkhoffMap_action_identity (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    ((hillOriginalBirkhoffMap q).val k).1^2+((hillOriginalBirkhoffMap q).val k).2^2 =
      2*hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 := by
  rw [hillOriginalBirkhoffMap_coordinates]
  exact hillOriginalBirkhoff_action_identity q ⟨k+1,by omega⟩

/-- The ONE fixed global real map carries the canonical Gardner matrix.
The germs match its ACTUAL raw coordinate functions on original source
neighborhoods, including every collapsed gap. -/
theorem exists_hillOriginalBirkhoffMap_canonical_germs (q : hillRealMeanZeroSourceSubmodule) :
    ∃ X Y : ℕ+ → PeriodOneHminusOne → ℂ,
      (∀ n : ℕ+,
        AnalyticAt ℂ (X n) (hillOriginalHminusSource q.val.val) ∧
        AnalyticAt ℂ (Y n) (hillOriginalHminusSource q.val.val) ∧
        ∀ᶠ p : hillRealMeanZeroSourceSubmodule in 𝓝 q,
          X n (hillOriginalHminusSource p.val.val) = (((hillOriginalBirkhoffMap p).val ((n : ℕ)-1)).1 : ℂ) ∧
          Y n (hillOriginalHminusSource p.val.val) = (((hillOriginalBirkhoffMap p).val ((n : ℕ)-1)).2 : ℂ)) ∧
      ∀ n m : ℕ+,
        NLS.Poisson.hminusGardnerBracket (X n) (X m) (hillOriginalHminusSource q.val.val) = 0 ∧
        NLS.Poisson.hminusGardnerBracket (X n) (Y m) (hillOriginalHminusSource q.val.val) =
          (if (n : ℕ) = (m : ℕ) then 1 else 0) ∧
        NLS.Poisson.hminusGardnerBracket (Y n) (X m) (hillOriginalHminusSource q.val.val) =
          -(if (n : ℕ) = (m : ℕ) then 1 else 0) ∧
        NLS.Poisson.hminusGardnerBracket (Y n) (Y m) (hillOriginalHminusSource q.val.val) = 0 := by
  obtain ⟨X,Y,hS,hM⟩ := exists_hillOriginalRealBirkhoff_canonical_germs q
  refine ⟨X,Y,?_,hM⟩
  intro n
  refine ⟨(hS n).1,(hS n).2.1,?_⟩
  have hQ : Continuous (fun p : hillRealMeanZeroSourceSubmodule =>
      (⟨p.val.val,p.val.property⟩ : RealPeriodOneHillPotential)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  filter_upwards [hQ.continuousAt.tendsto.eventually (hS n).2.2] with p hp
  have hn : (⟨(n : ℕ)-1+1,by have := n.pos; omega⟩ : ℕ+) = n := by
    apply Subtype.ext
    change (n : ℕ)-1+1 = (n : ℕ)
    have := n.pos
    omega
  rw [hillOriginalBirkhoffMap_coordinates,hn]
  simpa [hillOriginalBirkhoffX,hillOriginalBirkhoffY] using hp

end NLS.KdV
