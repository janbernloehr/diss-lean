import NLS.ZakharovShabat.SourceAbelianEndpointIntegrals
import NLS.ZakharovShabat.SourceAdmissibleEndpointPath

/-!
# Section 19's original improper integrals on admissible paths

Every interior C¹ admissible path from either endpoint to an off-cut point
has an improper integral equal to the canonical primitive. The limits use
actual truncated integrals and independent endpoint parameters. Finite
piecewise C¹ paths are included without an absolute-integrability hypothesis.
-/
noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- Both original endpoints have the same zero limit on the full cut complement. -/
theorem normalized_endpoint_limit (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (𝓝[sourceCanonicalRootDomain hp hp1 ψ] a) (𝓝 0) := by
  simpa only [sub_self,mul_zero] using
    (C.fullPrimitive_endpoint_limit_openGap n n ψ hψ a ha).mono_left
      (nhdsWithin_mono a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))

/-- Every admissible interior C¹ path computes the original endpoint integral. -/
theorem endpointPath_integral (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (γ : Path a ν)
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) (hadm : SourceAdmissiblePath hp hp1 ψ γ) :
    Tendsto (fun t : ℝ × ℝ => truncatedPathIntegral (sourceAbelianDifferential hp hp1 ψ) γ t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
      (𝓝 (sourceFullAbelianPrimitive hp hp1 W n (ν,ψ))) ∧
    improperPathIntegral (sourceAbelianDifferential hp hp1 ψ) γ =
      sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have hlim := tendsto_truncatedPathIntegral_of_primitive_boundary
    (sourceAbelianDifferential hp hp1 ψ) (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
    (sourceCanonicalRootDomain hp hp1 ψ) (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn
    (fun z hz => sourceFullAbelianPrimitive_hasDerivAt E n z hz) γ hγ hadm
    (C.normalized_endpoint_limit ψ hψ n a ha)
    ((sourceFullAbelianPrimitive_hasDerivAt E n ν hν).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [sub_zero] at hlim
  exact ⟨hlim,hlim.limUnder_eq⟩

/-- Corners preserve the genuine improper integral and its path-independent value. -/
theorem endpointPiecewisePath_integral (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (Γ : PiecewiseInteriorC1Path a ν)
    (hadm : SourceAdmissiblePiecewisePath hp hp1 ψ Γ) :
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral (sourceAbelianDifferential hp hp1 ψ) t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
      (𝓝 (sourceFullAbelianPrimitive hp hp1 W n (ν,ψ))) ∧
    Γ.improperIntegral (sourceAbelianDifferential hp hp1 ψ) =
      sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have haCut : a ∈ sourcePeriodicSegment hp hp1 ψ n := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hcount : Γ.count ≠ 0 := by
    intro hz
    have he : a = ν := Γ.initial.symm.trans (hz ▸ Γ.terminal)
    exact hν n (he ▸ haCut)
  let F := fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
  let L : ℕ → ℂ := fun k => if k = 0 then 0 else F (Γ.vertex k)
  have hL (k : ℕ) (hk : k ≤ Γ.count) :
      Tendsto F (𝓝[sourceCanonicalRootDomain hp hp1 ψ] (Γ.vertex k)) (𝓝 (L k)) := by
    by_cases hk0 : k = 0
    · subst k
      simpa only [L,if_pos rfl,Γ.initial] using C.normalized_endpoint_limit ψ hψ n a ha
    have hkD : Γ.vertex k ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      by_cases hkc : k = Γ.count
      · simpa only [hkc,Γ.terminal] using hν
      · exact hadm.2 k (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkc)
    simpa only [L,if_neg hk0] using
      (sourceFullAbelianPrimitive_hasDerivAt E n (Γ.vertex k) hkD).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := sourceCanonicalRootDomain hp hp1 ψ))
  have hlim := Γ.tendsto_truncatedIntegral_of_primitive_boundary (sourceAbelianDifferential hp hp1 ψ)
    F (sourceCanonicalRootDomain hp hp1 ψ) (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn
    (fun z hz => sourceFullAbelianPrimitive_hasDerivAt E n z hz) hadm.1 L hL
  simp only [L,if_neg hcount,if_pos rfl,Γ.terminal,sub_zero,F] at hlim
  exact ⟨hlim,hlim.limUnder_eq⟩

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
