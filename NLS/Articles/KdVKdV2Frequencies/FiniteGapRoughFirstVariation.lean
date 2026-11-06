import NLS.Articles.KdVKdV2Frequencies.NativePhysicalHamiltonianVariations
import NLS.Articles.KdVKdV2Frequencies.NativeContourActionDifferentials
import NLS.SequenceSpaces.PhysicalRealMeanZeroComplexSpan

/-! # A genuine rough action functional carrying the physical finite-gap first variation

The finite action combination is not asserted to extend the physical
Hamiltonian. Its ACTUAL rough differential agrees with the independently
defined native H_m differential on EVERY complex mean-zero native direction.
Its Gardner vector is the exact finite combination of physical action vectors.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The intrinsic original hierarchy frequency evaluated at the SAME native source. -/
def nativeSourceHierarchyFrequency (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) : ℝ :=
  D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)) n

/-- A finite analytic action combination with the fixed physical frequencies
at q. Only its first variation at that source is compared with physical H_m. -/
def finiteGapActionCombination (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (u : PeriodOneHminusOne) : ℂ :=
  ∑ n ∈ S, (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ)*D.roughActionCoordinate n u

theorem finiteGapActionCombination_analytic (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+) :
    AnalyticOnNhd ℂ (D.finiteGapActionCombination m r hrs q S) D.domain := by
  intro u hu
  exact Finset.analyticAt_fun_sum S (fun n _ => analyticAt_const.mul (D.roughActionCoordinate_analytic n u hu))

/-- The actual rough Banach differential is the finite sum of original action differentials. -/
theorem hasFDerivAt_finiteGapActionCombination (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (u : PeriodOneHminusOne) (hu : u ∈ D.domain) :
    HasFDerivAt (D.finiteGapActionCombination m r hrs q S)
      (∑ n ∈ S, (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ) •
        fderiv ℂ (D.roughActionCoordinate n) u) u := by
  simpa only [smul_eq_mul] using!
    HasFDerivAt.fun_sum (fun n _ =>
      (D.roughActionCoordinate_analytic n u hu).differentiableAt.hasFDerivAt.const_smul
        (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ))

/-- Actual physical finite-gap first variations determine the rough action
combination differential on ALL complex mean-zero native directions. This is
an equality of genuine differentials, without assuming a spectral frequency identity. -/
theorem finiteGapActionCombination_fderiv_matches_native
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0)
    (h : ScalarSobolev m) (hm : h.val 0=0) :
    (fderiv ℂ (nativeHillHierarchyHamiltonian m) q.val) h =
      (fderiv ℂ (D.finiteGapActionCombination m r hrs q S) (nativeHillSource m q.val))
        (nativeHillSource m h) := by
  let u := nativeHillSource m q.val
  have hu : u ∈ D.domain := D.real_mem_domain _ (nativeHillSource_real m q.val q.property.1)
  let L := fderiv ℂ (nativeHillHierarchyHamiltonian m) q.val
  let M := (fderiv ℂ (D.finiteGapActionCombination m r hrs q S) u).comp (nativeHillSource m)
  have he (a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) : L a.val=M a.val := by
    change (fderiv ℂ (nativeHillHierarchyHamiltonian m) q.val) a.val =
      (fderiv ℂ (D.finiteGapActionCombination m r hrs q S) u) (nativeHillSource m a.val)
    rw [←D.nativeSourceHierarchyHamiltonian_fderiv_eq_native m q a,
      D.nativeSourceHierarchyHamiltonian_fderiv_finite_gap m r hrs q S hq a,
      (D.hasFDerivAt_finiteGapActionCombination m r hrs q S u hu).fderiv]
    simp only [sum_apply,smul_apply,smul_eq_mul,
      nativeSourceHierarchyFrequency]
    apply Finset.sum_congr rfl
    intro n _
    rw [D.nativeSourceActionSequence_fderiv_eq_rough]
    ring
  simpa only [L,M,ContinuousLinearMap.comp_apply] using!
    clm_eq_on_meanZero_of_physical_real (Weight.sobolev (m : ℝ)) (Weight.sobolev_neg (m : ℝ)) L M he h hm

/-- The genuine Gardner vector is the finite weighted sum of original action vectors. -/
theorem finiteGapActionCombination_hamiltonianVector (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (u : PeriodOneHminusOne) (hu : u ∈ D.domain) :
    NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S) u =
      ∑ n ∈ S, (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ) •
        NLS.Poisson.gardnerHamiltonianVector (D.roughActionCoordinate n) u := by
  unfold NLS.Poisson.gardnerHamiltonianVector
  rw [(D.hasFDerivAt_finiteGapActionCombination m r hrs q S u hu).fderiv,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul]

/-- At the original physical source the entire vector has the ACTUAL
contour direction, with its previously verified Gardner sign and no gradient assumption. -/
theorem finiteGapActionCombination_physical_vector (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+) :
    NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S) (nativeHillSource m q.val) =
      ∑ n ∈ S, (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ) •
        (-hillOriginalHminusSource (hillPhysicalMomentHamiltonianSource
          (nativeHillPhysicalSource m q.val q.property.1).val
          (nativeHillPhysicalSource m q.val q.property.1).property.1
          (nativeHillPhysicalSource m q.val q.property.1).property.2 n n.pos 0)) := by
  have hp : nativeHillSource m q.val = hillOriginalHminusSource (nativeHillPhysicalSource m q.val q.property.1).val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact nativeHillSource_eq_physical m q.val q.property.1
  rw [D.finiteGapActionCombination_hamiltonianVector m r hrs q S _
    (D.real_mem_domain _ (nativeHillSource_real m q.val q.property.1))]
  apply Finset.sum_congr rfl
  intro n _
  rw [hp,D.roughActionCoordinate_hamiltonianVector]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
