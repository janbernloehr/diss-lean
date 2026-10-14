import NLS.ZakharovShabat.SourceAdmissibleEndpointPath

/-!
# Lemma 10.11 on the unchanged common source domain

The package retains the analytic continuation across every collapsed gap
and zero periods on all original disks. It adds the endpoint assertion
for every admissible path of the usual piecewise C¹ class, allowing even
C¹ regularity only in the interiors of its pieces. Endpoint integration
is an independently truncated improper limit of actual path integrals.
-/

noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both parts of Lemma 10.11, including cornered admissible endpoint paths. -/
structure SourceLemma10_11Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma10_11CircleData hp hp1 W
  endpoint_paths : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c →
    ∀ ψ ∈ W, ψ ∈ V → ∀ n : ℤ,
    ∀ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n),
    ContDiffOn ℝ 1 γ.extend (Ioo 0 1) → SourceAdmissiblePath hp hp1 ψ γ → range γ ⊆ D n →
    Tendsto (fun t : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) γ t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 0) ∧
    improperPathIntegral (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) γ = 0
  piecewise_paths : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c →
    ∀ ψ ∈ W, ψ ∈ V → ∀ n : ℤ,
    ∀ Γ : PiecewiseInteriorC1Path
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n),
    SourceAdmissiblePiecewisePath hp hp1 ψ Γ → (∀ i u, Γ.edge i u ∈ D n) →
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral
      (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 0) ∧
    Γ.improperIntegral (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0

/-- Finish the endpoint assertion while retaining W and all original disks. -/
theorem SourceLemma10_11CircleData.admissibleEndpoints
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) : SourceLemma10_11Data hp hp1 W where
  previous := h
  endpoint_paths := h.endpointPath_zero
  piecewise_paths := h.endpointPiecewisePath_zero

/-- Lemma 10.11 for every finite p>1, on the common open connected
neighborhood of the entire real-type locus retained from Section 10. -/
theorem sourceLemma10_11 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_11Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_11CirclePeriods hp hp1
  exact ⟨W,ho,hc,hr,h.admissibleEndpoints⟩

end NLS.ZakharovShabat
