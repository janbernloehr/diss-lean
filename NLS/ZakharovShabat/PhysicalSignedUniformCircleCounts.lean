import NLS.ZakharovShabat.ClassicalSignedCircleCounts
import NLS.ZakharovShabat.CentralDeformation
import NLS.ZakharovShabat.ParityClusterMultiplicity

/-! # Locally uniform physical signed counts on the literal central circle -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Metric Set
namespace NLS.ZakharovShabat

/-- On one open convex physical L² neighborhood, every sufficiently large circle
of radius `(2N+1/2)π` avoids both signed spectra and contains exactly `4N+2`
periodic and `4N` antiperiodic eigenvalues, counted with their actual physical
generalized-eigenspace dimensions. The same neighborhood contains zero. -/
theorem exists_uniform_physicalSignedCircleCounts (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ U : Set IntervalPairL2,
      IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
        sphere (0 : ℂ) ((2*(N : ℝ)+1/2)*Real.pi) ⊆ classicalSignedResolventSet v r ∧
        (∑ z ∈ enclosedClassicalSignedSpectrum v r 0 ((2*(N : ℝ)+1/2)*Real.pi),
          classicalSignedAlgebraicMultiplicity v r z) =
          if r % 2 = 0 then 4*N+2 else 4*N := by
  let F : IntervalPairL2 →L[ℂ] PairSpace 2 :=
    periodOnePotential.comp sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨K₀,V,hK₀,hoV,hcV,huV,h0V,hV⟩ := exists_uniform_centralCircle (by simp) (F u)
  obtain ⟨L₀,W,_,hoW,hcW,huW,h0W,hW⟩ :=
    exists_uniform_central_parity_multiplicity_sums (by simp) (F u)
  refine ⟨max K₀ L₀,by omega,F ⁻¹' (V ∩ W),
    (hoV.inter hoW).preimage F.continuous,
    (hcV.inter hcW).linear_preimage (F.restrictScalars ℝ).toLinearMap,
    ⟨huV,huW⟩,by simpa only [Set.mem_preimage,map_zero,Set.mem_inter_iff] using And.intro h0V h0W,?_⟩
  intro v hv N hN r
  have hcircle := hV (F v) hv.1 (2*N) (by omega)
  have hcount := hW (F v) hv.2 (periodOnePotential_mem _) (2*N) (by omega) r
  dsimp only [F,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at hcircle hcount
  have hR : centralCircleRadius (2*N) = (2*(N : ℝ)+1/2)*Real.pi := by
    unfold centralCircleRadius
    push_cast
    ring
  refine ⟨classicalSignedCircle_subset_resolvent v r 0 _ (by simpa only [hR] using hcircle.2.1),?_⟩
  rw [sum_enclosedClassicalSignedSpectrum_eq,← hR,hcircle.2.2.1]
  have he : ((2*N : ℕ) : ℤ) % 2 = 0 := by omega
  simpa only [he,eq_comm (a := (0 : ℤ)),show 2*(2*N) = 4*N by omega] using hcount

end NLS.ZakharovShabat
