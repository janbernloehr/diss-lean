import NLS.ZakharovShabat.AppendixFOriginalCollapsed

/-!
# Source neighborhoods for the collapsed restriction in Appendix F

The existing Cauchy families cover an open connected neighborhood of
the real source locus inside any prescribed open neighborhood. Intersecting
with the Section 10 isolating neighborhoods keeps their spectral discs and
supplies the chart cover needed by the original-disc collapsed formula.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p}

/-- Cauchy source charts cover a connected almost-real neighborhood inside a prescribed domain. -/
theorem exists_appendixF_source_chart_cover (S : Set (CoeffPair p))
    (hS : IsOpen S) (hrealS : realTypeSourceLocus p ⊆ S) :
    ∃ W U : Set (CoeffPair p), IsOpen W ∧ IsOpen U ∧ IsConnected U ∧
      realTypeSourceLocus p ⊆ U ∧ U ⊆ S ∧ U ⊆ W ∧
      ∀ ψ ∈ U, ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ψ ∈ ball C.discs.source.val C.discs.sourceRadius := by
  classical
  obtain ⟨W,hW,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  choose C hC using hfamilies
  let T : Set (CoeffPair p) := S ∩ ⋃ φ : realTypeSourceSubmodule p,
    ball (C φ).discs.source.val (C φ).discs.sourceRadius
  have hT : IsOpen T := hS.inter (isOpen_iUnion (fun _ => isOpen_ball))
  have hrealT : realTypeSourceLocus p ⊆ T := by
    intro φ hφ
    refine ⟨hrealS hφ,mem_iUnion.mpr ⟨⟨φ,hφ⟩,?_⟩⟩
    rw [hC]
    exact mem_ball_self (C ⟨φ,hφ⟩).discs.sourceRadius_pos
  let U := connectedComponentIn T (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealT
  have hUT : U ⊆ T := connectedComponentIn_subset T 0
  have hcharts (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ψ ∈ ball C.discs.source.val C.discs.sourceRadius := by
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUT hψ).2
    exact ⟨C φ,hφ⟩
  refine ⟨W,U,hW,hT.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr (hrealT hzero),hrealU,
    fun ψ hψ => (hUT hψ).1,?_,hcharts⟩
  intro ψ hψ
  obtain ⟨C,hψC⟩ := hcharts ψ hψ
  exact C.discs.source_subset hψC

/-- One local source neighborhood supplies all original-disc collapsed analytic restrictions. -/
theorem SourceLemma10_10Data.appendixF_local_collapsed_analytic_extensions
    {S U W : Set (CoeffPair p)} (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (hU : IsOpen U) (hUS : U ⊆ S)
    (hcharts : ∀ ψ ∈ U, ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
      ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (φ : CoeffPair p) (hφ : φ ∈ U) :
    ∃ V : Set (CoeffPair p), ∃ D : ℤ → Set ℂ, ∃ c : ℝ,
      IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ U ∧
      SourceIsolatingNeighborhoods hp hp1 V D c ∧
      ∀ n : ℤ, ∀ ν ∈ frontier (D n),
        ∃ G : CoeffPair p → ℂ, AnalyticOnNhd ℂ G V ∧
          ∀ ψ ∈ V, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
            G ψ = sourceAbelianEndpointAverage hp hp1 n ν ψ := by
  obtain ⟨B,hB,_,hφB,_,D,c,hD⟩ :=
    H.previous.previous.previous.roots.roots.symmetric.isolation φ (hUS hφ)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp ((hU.inter hB).mem_nhds ⟨hφ,hφB⟩)
  have hVU : ball φ r ⊆ U := fun ψ hψ => (hrsub hψ).1
  have hD' : SourceIsolatingNeighborhoods hp hp1 (ball φ r) D c :=
    hD.mono (fun ψ hψ => (hrsub hψ).2)
  refine ⟨ball φ r,D,c,isOpen_ball,isConnected_ball hr,mem_ball_self hr,hVU,hD',?_⟩
  intro n ν hν
  exact H.appendixF_original_collapsed_analytic_extension hS isOpen_ball (hVU.trans hUS)
    hD' (fun ψ hψ => hcharts ψ (hVU hψ)) n ν hν

/-- The collapsed restriction has local analytic extensions without a supplied chart-cover hypothesis.
One source neighborhood and isolating family work for every index and boundary point. -/
theorem exists_appendixF_collapsed_analytic_extensions :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ ∈ U, ∃ V : Set (CoeffPair p), ∃ D : ℤ → Set ℂ, ∃ c : ℝ,
        IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ U ∧
        SourceIsolatingNeighborhoods hp hp1 V D c ∧
        ∀ n : ℤ, ∀ ν ∈ frontier (D n),
          ∃ G : CoeffPair p → ℂ, AnalyticOnNhd ℂ G V ∧
            ∀ ψ ∈ V, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
              G ψ = sourceAbelianEndpointAverage hp hp1 n ν ψ := by
  obtain ⟨S,hS,_,hrealS,H⟩ := sourceLemma10_10 hp hp1
  obtain ⟨W,U,_,hU,hUc,hrealU,hUS,_,hcharts⟩ :=
    exists_appendixF_source_chart_cover (hp := hp) (hp1 := hp1) S hS hrealS
  exact ⟨U,hU,hUc,hrealU,fun φ hφ =>
    H.appendixF_local_collapsed_analytic_extensions hS hU hUS hcharts φ hφ⟩

end NLS.ZakharovShabat
