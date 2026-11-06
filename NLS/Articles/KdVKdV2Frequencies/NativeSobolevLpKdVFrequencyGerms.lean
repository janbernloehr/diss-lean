import NLS.KdV.PhysicalSobolevLpFrequencyChart
import NLS.Articles.KdVConvexity.PhysicalMiuraFrequencyRecovery

/-! Actual native Hamiltonian frequencies are the coefficients of the
unweighted ellr germs on H^(-1/2). This is the physical-source estimate
needed for the stronger action targets of Theorem 1.2(i); action descent
in those stronger norms is a separate obligation. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def nativeHalfSobolevSource : ScalarSobolev 1 →L[ℂ] HalfSobolevHillSource :=
  WeightedCoeff.sobolevInclusion (by norm_num : (1/2 : ℝ)-1≤(1 : ℕ))

@[simp] theorem nativeHalfSobolevSource_apply (q : ScalarSobolev 1) (n : ℤ) :
    (nativeHalfSobolevSource q).val n=q.val n :=
  WeightedCoeff.sobolevInclusion_apply _ q n

theorem nativeHalfSobolevSource_inclusion (q : ScalarSobolev 1) :
    halfSobolevHillInclusion (nativeHalfSobolevSource q)=nativeHillSource 1 q := by
  apply Subtype.ext
  funext n
  rw [periodOneSobolevImageInclusion_apply,nativeHalfSobolevSource_apply,nativeHillSource_apply]

theorem nativeHalfSobolevSource_physical
    (p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    halfSobolevHillInclusion (nativeHalfSobolevSource p.val)=
      hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val := by
  rw [nativeHalfSobolevSource_inclusion,hillOriginalHminusSource_eq_physical]
  exact nativeHillSource_eq_physical 1 p.val p.property.1

theorem native_half_sobolev_physical_frequency_recovery
    (D : GlobalRoughAbelianForwardData) (B : PhysicalMiuraFrequencyChart)
    (p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)))
    (hp : halfSobolevHillInclusion (nativeHalfSobolevSource p.val)∈B.domain) (n : ℕ+) :
    B.correction n (halfSobolevHillInclusion (nativeHalfSobolevSource p.val))=
      (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) p n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  have hm : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val∈B.domain :=
    (nativeHalfSobolevSource_physical p) ▸ hp
  exact (congrArg (B.correction n) (nativeHalfSobolevSource_physical p)).trans
    (native_physical_frequency_eq_miura_chart D B p hm n).symm

theorem native_half_sobolev_packet_recovery
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (U : Set HalfSobolevHillSource)
    (B : PhysicalMiuraFrequencyChart) (F : HalfSobolevHillSource → Coeff r)
    (hsub : ∀ a∈U, halfSobolevHillInclusion a∈B.domain)
    (hrec : ∀ a∈U, ∀ n : ℕ+, F a (n : ℤ)=B.correction n (halfSobolevHillInclusion a))
    (D : GlobalRoughAbelianForwardData)
    (p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)))
    (hp : nativeHalfSobolevSource p.val∈U) (n : ℕ+) :
    F (nativeHalfSobolevSource p.val) (n : ℤ)=
      (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) p n : ℂ)-(2*(n : ℂ)*Real.pi)^3 :=
  (hrec _ hp n).trans (native_half_sobolev_physical_frequency_recovery D B p (hsub _ hp) n)

theorem nativeHalfSobolevSource_real
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    IsRealPeriodOneHminusOne (halfSobolevHillInclusion (nativeHalfSobolevSource q.val)) := by
  rw [nativeHalfSobolevSource_inclusion]
  exact nativeHillSource_real 1 q.val q.property.1

theorem exists_native_physicalSobolevLpFrequencyChart
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    ∃ B : PhysicalSobolevLpFrequencyChart r, nativeHalfSobolevSource q.val∈B.domain :=
  exists_physicalSobolevLpFrequencyChart hr _ (nativeHalfSobolevSource_real q)

end NLS.Articles.KdVKdV2Frequencies
