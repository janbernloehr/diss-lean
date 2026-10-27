import NLS.ZakharovShabat.PhysicalSignedEnumerationComparison

/-! # One local cutoff for the separate and combined physical spectral lists -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open NLS.ComplexAnalysis Set
namespace NLS.ZakharovShabat

/-- A complete source construction at any cutoff identifies the physical signed
lists with the combined endpoints outside that cutoff. No selected canonical
cutoff, and no continuity of individual complex roots, enters the bound. -/
theorem physicalSignedPairs_eq_periodic_of_complete (u : IntervalPairL2)
    {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs (by simp) SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) N ξ η)
    (r : Fin 2) (n : ℤ) (hn : N < (2*n+(r.val : ℤ)).natAbs) :
    physicalSignedLeft u r n = physicalPeriodicLeft u (2*n+(r.val : ℤ)) ∧
      physicalSignedRight u r n = physicalPeriodicRight u (2*n+(r.val : ℤ)) := by
  have he : weightedBaseToPair SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) =
      periodOnePotential (sourcePhysicalL2Equiv.symm u) := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨a,b,hs,hsw,hso,_⟩ := h.exists_parity_ordered
  obtain ⟨c,d,hf,hfw,hfo,_⟩ := h.toEndpoints.exists_ordered
  have hd := hs.toEndpoints
  rw [he] at hd hf
  have hcan := hf.eq_canonicalPeriodicEndpoints (by norm_num) (periodOnePotential_mem _) hfw hfo
  have hsign := physicalSignedPairs_eq_of_complete u r hs hsw hso
  rw [hsign.1,hsign.2,(physicalPeriodicEndpoints_eq_source u).1,
    (physicalPeriodicEndpoints_eq_source u).2,← hcan.1,← hcan.2]
  exact (hd.distant _ hn).ordered_unique (hf.distant _ hn) (hsw _) (hfw _)

/-- The physical signed lists and the combined physical endpoints agree with
the printed indices `2n` and `2n+1` outside one cutoff on an open convex L²
neighborhood. Every larger cutoff works throughout that same neighborhood. -/
theorem exists_uniform_physicalSignedPairs_eq_periodic (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set IntervalPairL2,
      IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ r : Fin 2, ∀ n : ℤ, N < n.natAbs →
        physicalSignedLeft v r n = physicalPeriodicLeft v (2*n+(r.val : ℤ)) ∧
        physicalSignedRight v r n = physicalPeriodicRight v (2*n+(r.val : ℤ)) := by
  let F : IntervalPairL2 →L[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight 2 :=
    unitBaseEquiv.symm.toContinuousLinearMap.comp
      (periodOnePotential.comp sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have he (v : IntervalPairL2) : weightedBaseToPair SpectralWeight.one (F v) =
      periodOnePotential (sourcePhysicalL2Equiv.symm v) := by
    change weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm _) = _
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨N₀,hN₀,V,ho,hc,hu,h0,hV⟩ :=
    exists_uniform_completePeriodicParityPairs (by simp) (by norm_num) SpectralWeight.one (F u)
  refine ⟨N₀,hN₀,F ⁻¹' V,ho.preimage F.continuous,
    hc.linear_preimage (F.restrictScalars ℝ).toLinearMap,hu,by simpa using h0,?_⟩
  intro v hv N hN r n hn
  obtain ⟨ξ,η,h⟩ := hV (F v) hv (by rw [he]; exact periodOnePotential_mem _) (2*N) (by omega)
  exact physicalSignedPairs_eq_periodic_of_complete v h r n (by have := r.isLt; omega)

end NLS.ZakharovShabat
