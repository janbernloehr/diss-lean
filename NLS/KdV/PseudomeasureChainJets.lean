import NLS.KdV.SingularHillChains

/-!
# Analytic finite-jet identities for actual physical root chains

The physical chain polynomial and its resonant polynomial differ from their
analytic reconstructions by a chain-length power times an analytic function.
Thus every lower Taylor derivative of the reduced residual vanishes. All
coefficients remain in the original H1 domain throughout this argument.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis

/-- The final physical chain coefficient as endpoint data, also for the empty chain. -/
def endpointHillChainForcing (r : ℝ) (hr : 0 ≤ r) (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  H1EndpointInclusion r hr (pencilChainEndpoint
    (LinearMap.id : FourierLebesgueSpace (2:ℝ) 1 2 →ₗ[ℂ] FourierLebesgueSpace (2:ℝ) 1 2) N v)

/-- The analytic remainder in the finite resonant equation. -/
def endpointHillChainReducedRemainder (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2) (t : ℂ) : ℂ × ℂ :=
  hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
    (endpointInverseFamily r hr hr1 n (q,z+t) (endpointHillChainForcing r hr N v))

/-- The analytic remainder in the original H1 reconstruction. -/
def endpointHillChainReconstructionRemainder (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2) (t : ℂ) : FourierLebesgueSpace (2:ℝ) 1 2 :=
  endpointResponseFamily r hr hr1 n (q,z+t) (endpointHillChainForcing r hr N v)

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
variable (N : ℕ) (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2)

include hn hs in
/-- The finite resonant remainder is analytic in its spectral increment. -/
theorem analyticAt_endpointHillChainReducedRemainder (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointHillChainReducedRemainder r hr hr1 n q z N v) 0 := by
  have hK : AnalyticAt ℂ (endpointInverseFamily r hr hr1 n) (q,z+(0:ℂ)) := by
    simpa only [add_zero] using analyticAt_endpointInverseFamily r hr hr1 n hn (q,z) hz hs
  have hP : AnalyticAt ℂ (fun t : ℂ => (q,z+t)) 0 :=
    analyticAt_const.prod (analyticAt_const.add analyticAt_id)
  have hA := hK.comp (f := fun t : ℂ => (q,z+t)) hP
  let e := (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
    (ContinuousLinearMap.apply ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
      (endpointHillChainForcing r hr N v))
  exact (e.analyticAt _).comp hA

include hn hs in
/-- The reconstruction remainder is analytic in the full original H1 norm. -/
theorem analyticAt_endpointHillChainReconstructionRemainder (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointHillChainReconstructionRemainder r hr hr1 n q z N v) 0 := by
  have hG : AnalyticAt ℂ (endpointResponseFamily r hr hr1 n) (q,z+(0:ℂ)) := by
    simpa only [add_zero] using analyticAt_endpointResponseFamily r hr hr1 n hn (q,z) hz hs
  have hP : AnalyticAt ℂ (fun t : ℂ => (q,z+t)) 0 :=
    analyticAt_const.prod (analyticAt_const.add analyticAt_id)
  let e := ContinuousLinearMap.apply ℂ (FourierLebesgueSpace (2:ℝ) 1 2)
    (endpointHillChainForcing r hr N v)
  exact (e.analyticAt _).comp (f := fun t : ℂ => endpointResponseFamily r hr hr1 n (q,z+t))
    (hG.comp (f := fun t : ℂ => (q,z+t)) hP)

/-- Every sufficiently small spectral increment remains in the corrected strip. -/
theorem eventually_shift_mem_reducedHillStrip (m : ℕ) (a : ℂ)
    (ha : |a.re-freeHillValue m| < 6*(m:ℝ)) :
    ∀ᶠ t in 𝓝 (0:ℂ), a+t ∈ reducedHillStrip m := by
  have ht : Tendsto (fun t : ℂ => a+t) (𝓝 0) (𝓝 a) := by
    have hc : Continuous (fun t : ℂ => a+t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0:ℂ)
  exact ht.eventually (eventually_mem_reducedHillStrip m a ha)

include hn hs in
/-- The exact reduced residual of every physical N-chain is divisible, as
an analytic germ, by the Nth power of the spectral increment. -/
theorem endpointHillChain_reduced_germ
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (hv : v ∈ singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N) :
    (fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t)
      (endpointHillH1Coordinates n (pencilChainPolynomial N v t))) =ᶠ[𝓝 0]
      (fun t : ℂ => t^N • endpointHillChainReducedRemainder r hr hr1 n q z N v t) := by
  filter_upwards [eventually_shift_mem_reducedHillStrip n z hz] with t ht
  have hE := endpointHillChainPolynomial_forcing r hr hr1 q z N v hv t
  have hR := endpointPhysicalPencil_inhomogeneous_reduced r hr hr1 n hn (z+t) ht q hs
    (t^N • endpointHillChainForcing r hr N v) (pencilChainPolynomial N v t) hE
  simpa only [map_smul, endpointHillChainReducedRemainder] using hR

include hn hs in
/-- The physical chain polynomial and its analytic resonant lift have the
same finite H1 jet, with an explicit analytic Nth-power error. -/
theorem endpointHillChain_reconstruction_germ
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (hv : v ∈ singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N) :
    (fun t : ℂ => pencilChainPolynomial N v t -
      endpointReconstructionFamily r hr hr1 n (q,z+t)
        (endpointHillH1Coordinates n (pencilChainPolynomial N v t))) =ᶠ[𝓝 0]
      (fun t : ℂ => t^N • endpointHillChainReconstructionRemainder r hr hr1 n q z N v t) := by
  filter_upwards [eventually_shift_mem_reducedHillStrip n z hz] with t ht
  have hE := endpointHillChainPolynomial_forcing r hr hr1 q z N v hv t
  have hR := endpointPhysicalPencil_inhomogeneous_reconstruct r hr hr1 n hn (z+t) ht q hs
    (t^N • endpointHillChainForcing r hr N v) (pencilChainPolynomial N v t) hE
  rw [map_smul] at hR
  exact sub_eq_iff_eq_add.mpr (hR.trans (add_comm _ _))

include hn hs in
/-- Every derivative below the chain length of the actual reduced residual is zero. -/
theorem endpointHillChain_reduced_derivatives_zero
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (hv : v ∈ singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N)
    (k : ℕ) (hk : k < N) :
    iteratedDeriv k (fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t)
      (endpointHillH1Coordinates n (pencilChainPolynomial N v t))) 0 = 0 :=
  NLS.ComplexAnalysis.iteratedDeriv_eq_zero_of_powered_germ
    (analyticAt_endpointHillChainReducedRemainder r hr hr1 n hn q z hs N v hz.le)
    N (endpointHillChain_reduced_germ r hr hr1 n hn q z hs N v hz hv) k hk

include hn hs in
/-- Every derivative below the chain length of the original H1 reconstruction error is zero. -/
theorem endpointHillChain_reconstruction_derivatives_zero
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (hv : v ∈ singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N)
    (k : ℕ) (hk : k < N) :
    iteratedDeriv k (fun t : ℂ => pencilChainPolynomial N v t -
      endpointReconstructionFamily r hr hr1 n (q,z+t)
        (endpointHillH1Coordinates n (pencilChainPolynomial N v t))) 0 = 0 :=
  NLS.ComplexAnalysis.iteratedDeriv_eq_zero_of_powered_germ
    (analyticAt_endpointHillChainReconstructionRemainder r hr hr1 n hn q z hs N v hz.le)
    N (endpointHillChain_reconstruction_germ r hr hr1 n hn q z hs N v hz hv) k hk

include hr hn hs in
/-- On every finite physical chain space the coefficientwise two-mode
projection is injective. No domain information is lost by its finite jet. -/
theorem endpointHillChainCoordinates_injective
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    Function.Injective (singularHillChainCoordinates
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z N n) := by
  intro x y he
  let d : singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N := x-y
  have hC (j : Fin N) : endpointHillH1Coordinates n (d.val j) = 0 := by
    have h := congrFun he j
    change endpointHillH1Coordinates n (x.val j) = endpointHillH1Coordinates n (y.val j) at h
    change endpointHillH1Coordinates n (x.val j-y.val j) = 0
    rw [map_sub, h, sub_self]
  have hpoly (t : ℂ) : endpointHillH1Coordinates n (pencilChainPolynomial N d.val t) = 0 := by
    unfold pencilChainPolynomial
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul, hC, smul_zero]
  have hrec := endpointHillChain_reconstruction_germ r hr hr1 n hn q z hs N d.val hz d.property
  have hE : pencilChainPolynomial N d.val =ᶠ[𝓝 0]
      fun t : ℂ => t^N • endpointHillChainReconstructionRemainder r hr hr1 n q z N d.val t := by
    filter_upwards [hrec] with t ht
    simpa only [hpoly, map_zero, sub_zero] using ht
  have hval := NLS.ComplexAnalysis.chainPolynomial_eq_zero_of_powered_germ N d.val
    (analyticAt_endpointHillChainReconstructionRemainder r hr hr1 n hn q z hs N d.val hz.le) hE
  have hd : d = 0 := Subtype.ext hval
  exact sub_eq_zero.mp hd

end NLS.KdV
