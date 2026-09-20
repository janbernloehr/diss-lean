import NLS.ZakharovShabat.HilbertDiscriminant

/-!
# Classical approximation of the intrinsic Hilbert discriminant

Classical traces of domain potentials converge to the intrinsic discriminant
whenever their coefficients converge in the Hilbert norm. No convergence in
the domain norm or bound on the representatives' supremum norms is required.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- Every convergent even domain approximation has the same pointwise spectral trace limit. -/
theorem tendsto_classicalDiscriminant_of_domainInclusion_tendsto
    {α : Type*} {l : Filter α} (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (a : α → Domain 2) (ha : ∀ i, a i ∈ domainParitySubspace 0)
    (hlim : Tendsto (fun i => domainInclusion (a i)) l (𝓝 φ)) (z : ℂ) :
    Tendsto (fun i => classicalDiscriminant (physicalDomainCurve (a i)) z)
      l (𝓝 (canonicalDiscriminant (by simp) φ z)) := by
  let ψ : α → pairParitySubspace (p := 2) 0 :=
    fun i => ⟨domainInclusion (a i), (mem_domainParitySubspace 0 (a i)).mp (ha i)⟩
  have hsub : Tendsto ψ l (𝓝 (⟨φ, hφ⟩ : pairParitySubspace (p := 2) 0)) :=
    tendsto_subtype_rng.mpr hlim
  have hc : Continuous (fun u : pairParitySubspace (p := 2) 0 =>
      canonicalDiscriminant (by simp) u.val z) :=
    (continuous_canonicalParityProduct_potential (by simp) (by norm_num) 0 (Or.inl rfl) z).add
      continuous_const
  have h := (hc.tendsto ⟨φ, hφ⟩).comp hsub
  change Tendsto (fun i => canonicalDiscriminant (by simp) (domainInclusion (a i)) z)
    l (𝓝 (canonicalDiscriminant (by simp) φ z)) at h
  apply h.congr'
  exact Eventually.of_forall (fun i => canonicalDiscriminant_domainInclusion (a i) (ha i) z)

/-- Fourier truncations give actual classical traces converging to the discriminant of any even Hilbert potential. -/
theorem tendsto_classicalDiscriminant_pairTruncateDomain (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    Tendsto (fun s : Finset ℤ => classicalDiscriminant (physicalDomainCurve (pairTruncateDomain s φ)) z)
      atTop (𝓝 (canonicalDiscriminant (by simp) φ z)) := by
  apply tendsto_classicalDiscriminant_of_domainInclusion_tendsto φ hφ (fun s => pairTruncateDomain s φ)
    (fun s => pairTruncateDomain_mem_parity s φ 0 hφ) _ z
  simpa only [domainInclusion_pairTruncateDomain] using tendsto_pairTruncate (by simp) φ

end NLS.ZakharovShabat
