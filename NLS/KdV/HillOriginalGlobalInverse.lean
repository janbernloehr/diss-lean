import NLS.KdV.HillOriginalLocalInverse
import NLS.FunctionalAnalysis.ClosedLocalHomeomorph

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.KdV

/-- The zero fiber of the ACTUAL original spectral map is the literal
zero source, by its exact original mean-zero L2 trace identity. -/
theorem hillOriginalMeanZeroRealSpectralMap_zero_fiber
    (q : hillRealMeanZeroSourceSubmodule)
    (hq : hillOriginalMeanZeroRealSpectralMap q = hillOriginalMeanZeroRealSpectralMap 0) : q = 0 := by
  apply norm_eq_zero.mp
  rw [←norm_hillOriginalMeanZeroRealSpectralMap q,hq,hillOriginalMeanZeroRealSpectralMap_zero,norm_zero]

/-- GLOBAL bijectivity of the ACTUAL original spectral sequence on its
ORIGINAL real mean-zero L2 domain. Every local inverse, properness and
the singleton zero fiber have been proved; none is an input hypothesis. -/
theorem bijective_hillOriginalMeanZeroRealSpectralMap :
    Function.Bijective hillOriginalMeanZeroRealSpectralMap :=
  NLS.FunctionalAnalysis.bijective_of_closed_localHomeomorph_singleton_fiber _
    isLocalHomeomorph_hillOriginalMeanZeroRealSpectralMap
    isProperMap_hillOriginalMeanZeroRealSpectralMap.isClosedMap 0
    hillOriginalMeanZeroRealSpectralMap_zero_fiber

/-- The ACTUAL ORIGINAL spectral map as a global homeomorphism, with
its original Banach spaces, topology and physical coordinate formula. -/
def hillOriginalMeanZeroSpectralHomeomorph :
    hillRealMeanZeroSourceSubmodule ≃ₜ lp (fun _ : ℕ => ℂ) 2 :=
  isLocalHomeomorph_hillOriginalMeanZeroRealSpectralMap.toHomeomorphOfBijective
    bijective_hillOriginalMeanZeroRealSpectralMap

@[simp] theorem hillOriginalMeanZeroSpectralHomeomorph_apply (q : hillRealMeanZeroSourceSubmodule) :
    hillOriginalMeanZeroSpectralHomeomorph q = hillOriginalMeanZeroRealSpectralMap q := rfl

/-- The inverse of the fixed actual original global spectral map. -/
def hillOriginalMeanZeroSpectralInverse : lp (fun _ : ℕ => ℂ) 2 → hillRealMeanZeroSourceSubmodule :=
  hillOriginalMeanZeroSpectralHomeomorph.symm

@[simp] theorem hillOriginalMeanZeroSpectralInverse_apply_map (q : hillRealMeanZeroSourceSubmodule) :
    hillOriginalMeanZeroSpectralInverse (hillOriginalMeanZeroRealSpectralMap q) = q :=
  hillOriginalMeanZeroSpectralHomeomorph.symm_apply_apply q

@[simp] theorem hillOriginalMeanZeroRealSpectralMap_apply_inverse (z : lp (fun _ : ℕ => ℂ) 2) :
    hillOriginalMeanZeroRealSpectralMap (hillOriginalMeanZeroSpectralInverse z) = z :=
  hillOriginalMeanZeroSpectralHomeomorph.apply_symm_apply z

/-- The global inverse is real Banach analytic at EVERY spectral sequence,
by agreement with the constructed actual local analytic inverses. -/
theorem analyticOnNhd_hillOriginalMeanZeroSpectralInverse :
    AnalyticOnNhd ℝ hillOriginalMeanZeroSpectralInverse univ := by
  intro z _
  let q := hillOriginalMeanZeroSpectralInverse z
  let e := hillOriginalLocalChart q
  have heq : hillOriginalMeanZeroRealSpectralMap q = z :=
    hillOriginalMeanZeroRealSpectralMap_apply_inverse z
  have he : hillOriginalMeanZeroSpectralInverse =ᶠ[𝓝 z] e.symm := by
    have ht : z ∈ e.target := by
      rw [←heq]
      exact e.map_source (hillOriginalLocalChart_mem_source q)
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    apply bijective_hillOriginalMeanZeroRealSpectralMap.1
    rw [hillOriginalMeanZeroRealSpectralMap_apply_inverse]
    exact (e.right_inv hy).symm
  have ha : AnalyticAt ℝ e.symm z := by
    rw [←heq]
    exact analyticAt_hillOriginalLocalInverse q
  exact ha.congr he.symm

/-- The actual global inverse is continuous in the ORIGINAL sequence/L2
topologies, independently of any higher-weight estimate. -/
theorem continuous_hillOriginalMeanZeroSpectralInverse : Continuous hillOriginalMeanZeroSpectralInverse :=
  hillOriginalMeanZeroSpectralHomeomorph.symm.continuous

end NLS.KdV
