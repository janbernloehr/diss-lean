import NLS.ZakharovShabat.AppendixFMidpointIdentity
import NLS.ZakharovShabat.AppendixFBoundaryIntegral

/-!
# Transport of the Appendix F limit to a fixed original boundary point

The finite connecting integral is analytic on the original source neighborhood
inside a Cauchy chart. Its analyticity follows from the joint primitive and the
actual polygonal-integral identity. Adding its limit transports the midpoint
argument's chosen boundary point to any fixed original boundary point.
-/

noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V S : Set (CoeffPair p)}
variable {D : ℤ → Set ℂ} {c : ℝ}

/-- Every original isolating boundary avoids all source gaps. -/
theorem SourceIsolatingNeighborhoods.appendixF_frontier_subset_rootDomain
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    frontier (D n) ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro ν hν
  have hopen : IsOpen (D n) := by
    obtain ⟨a,R,_,he⟩ := hD.discs n
    rw [he]
    exact isOpen_ball
  have hνnot : ν ∉ D n := by simpa only [hopen.interior_eq] using hν.2
  exact hD.closedCutDisk_subset_rootDomain ψ hψ n
    ⟨frontier_subset_closure hν,fun hs => hνnot (hD.gap ψ hψ n hs)⟩

/-- Connecting two original boundary points gives an analytic actual polygonal integral. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_original_boundary_integral_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (hV : IsOpen V) (hVC : V ⊆ ball C.discs.source.val C.discs.sourceRadius)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ)
    (μ ν : ℂ) (hμ : μ ∈ frontier (D n)) (hν : ν ∈ frontier (D n)) :
    AnalyticOnNhd ℂ (fun ψ => polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
      (sourceCanonicalRootDomain hp hp1 ψ) μ ν) V := by
  intro ψ hψ
  have hroot (z : ℂ) (hz : z ∈ frontier (D n)) :=
    hD.appendixF_frontier_subset_rootDomain ψ hψ n hz
  have hνA := (C.full_analytic n (ν,ψ) ⟨hVC hψ,hroot ν hν⟩).comp
    (f := fun χ : CoeffPair p => (ν,χ)) (analyticAt_const.prod analyticAt_id)
  have hμA := (C.full_analytic n (μ,ψ) ⟨hVC hψ,hroot μ hμ⟩).comp
    (f := fun χ : CoeffPair p => (μ,χ)) (analyticAt_const.prod analyticAt_id)
  apply (hνA.sub hμA).congr
  filter_upwards [hV.mem_nhds hψ] with χ hχ
  have hχμ := hD.appendixF_frontier_subset_rootDomain χ hχ n hμ
  have hχν := hD.appendixF_frontier_subset_rootDomain χ hχ n hν
  rw [C.polygonalIntegral_eq_endpointAverage_sub χ (hVC hχ) n μ ν hχμ hχν,
    C.endpointAverage_eq χ (hVC hχ) n ν hχν,C.endpointAverage_eq χ (hVC hχ) n μ hχμ]
  rfl

/-- The corrected midpoint argument converges at any fixed original boundary point. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_fixed_endpointAverage_limit
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hφC : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ψ : ℕ → CoeffPair p) (hψV : ∀ k, ψ k ∈ V) (hψ : Tendsto ψ atTop (𝓝 φ))
    (hopen : ∀ k, canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n ≠ 0)
    (ν : ℂ) (hν : ν ∈ frontier (D n)) :
    Tendsto (fun k => sourceAbelianEndpointAverage hp hp1 n ν (ψ k)) atTop
      (𝓝 (sourceAbelianEndpointAverage hp hp1 n ν φ)) := by
  obtain ⟨μ,hμ,hμlim⟩ := C.appendixF_exists_endpointAverage_limit H hS hV hVS hD φ hφ hφC n hgap
    ψ hψV hψ hopen
  have hA := C.appendixF_original_boundary_integral_analytic (hV.inter isOpen_ball)
    inter_subset_right (hD.mono inter_subset_left) n μ ν hμ hν
  have hi := (hA φ ⟨hφ,hφC⟩).continuousAt.tendsto.comp hψ
  have htotal := hμlim.add hi
  have heq := C.endpointAverage_eq_add_polygonalIntegral φ hφC n μ ν
    (hD.appendixF_frontier_subset_rootDomain φ hφ n hμ)
    (hD.appendixF_frontier_subset_rootDomain φ hφ n hν)
  rw [← heq] at htotal
  apply htotal.congr'
  filter_upwards [hψ (isOpen_ball.mem_nhds hφC)] with k hk
  exact (C.endpointAverage_eq_add_polygonalIntegral (ψ k) hk n μ ν
    (hD.appendixF_frontier_subset_rootDomain (ψ k) (hψV k) n hμ)
    (hD.appendixF_frontier_subset_rootDomain (ψ k) (hψV k) n hν)).symm

/-- Arbitrary mixtures of collapsed and open source gaps have the same fixed-boundary limit. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_mixed_endpointAverage_limit
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hφC : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ψ : ℕ → CoeffPair p) (hψV : ∀ k, ψ k ∈ V) (hψ : Tendsto ψ atTop (𝓝 φ))
    (ν : ℂ) (hν : ν ∈ frontier (D n)) :
    Tendsto (fun k => sourceAbelianEndpointAverage hp hp1 n ν (ψ k)) atTop
      (𝓝 (sourceAbelianEndpointAverage hp hp1 n ν φ)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  by_cases hopen : ∃ᶠ k in atTop, canonicalPeriodicGap hp hp1
      (periodOnePotential (ψ (ns k))) (periodOnePotential_mem (ψ (ns k))) n ≠ 0
  · obtain ⟨ms,hms,hgapms⟩ := exists_seq_forall_of_frequently hopen
    refine ⟨ms,?_⟩
    exact C.appendixF_fixed_endpointAverage_limit H hS hV hVS hD φ hφ hφC n hgap
      (fun k => ψ (ns (ms k))) (fun k => hψV (ns (ms k))) (hψ.comp (hns.comp hms)) hgapms ν hν
  · have hzero : ∀ᶠ k in atTop, canonicalPeriodicGap hp hp1
        (periodOnePotential (ψ (ns k))) (periodOnePotential_mem (ψ (ns k))) n = 0 := by
      simpa only [not_not] using not_frequently.mp hopen
    obtain ⟨G,hGA,hGeq⟩ := H.appendixF_original_collapsed_analytic_extension hS
      (hV.inter isOpen_ball) (inter_subset_left.trans hVS) (hD.mono inter_subset_left)
      (fun χ hχ => ⟨C,hχ.2⟩) n ν hν
    have hlim := (hGA φ ⟨hφ,hφC⟩).continuousAt.tendsto.comp (hψ.comp hns)
    rw [hGeq φ ⟨hφ,hφC⟩ hgap] at hlim
    refine ⟨id,hlim.congr' ?_⟩
    filter_upwards [hzero,(hψ.comp hns) (isOpen_ball.mem_nhds hφC)] with k hk hkC
    exact hGeq (ψ (ns k)) ⟨hψV (ns k),hkC⟩ hk

/-- The fixed-boundary endpoint average is continuous at a collapsed source, by the sequence argument. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_endpointAverage_continuousAt_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hφC : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (ν : ℂ) (hν : ν ∈ frontier (D n)) :
    ContinuousAt (sourceAbelianEndpointAverage hp hp1 n ν) φ := by
  have hwithin : ContinuousWithinAt (sourceAbelianEndpointAverage hp hp1 n ν) V φ := by
    apply tendsto_iff_seq_tendsto.mpr
    intro ψ hψ
    have hψφ : Tendsto ψ atTop (𝓝 φ) := hψ.mono_right nhdsWithin_le_nhds
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hψ.eventually self_mem_nhdsWithin)
    apply (tendsto_add_atTop_iff_nat N).mp
    exact C.appendixF_mixed_endpointAverage_limit H hS hV hVS hD φ hφ hφC n hgap
      (fun k => ψ (k+N)) (fun k => hN (k+N) (Nat.le_add_left N k))
      (hψφ.comp (tendsto_add_atTop_nat N)) ν hν
  exact hwithin.continuousAt (hV.mem_nhds hφ)

end NLS.ZakharovShabat
