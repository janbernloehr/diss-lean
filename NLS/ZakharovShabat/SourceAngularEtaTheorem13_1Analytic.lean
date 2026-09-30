import NLS.ZakharovShabat.SourceAngularEtaAnalyticPhase
import NLS.ZakharovShabat.SourceAngularEtaCauchyCommonDomain

/-!
# Theorem 13.1(ii): actual eta is analytic modulo pi

The original normalized psi family constructs full analytic eta charts
at every complex open gap on one neighborhood of the entire real locus.
Their representatives agree modulo pi, including opposite half-gap
branches and either periodic anchor. The phase `exp(2i eta)` is a
single nonzero analytic function on the open-gap source domain.
The chart APIs identify it with normalized integrable C1 admissible
spectral integrals, retaining actual and model integrability explicitly.
All beta results of (i) and (iii) coexist on the same source neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual eta has constructed analytic representatives modulo pi at
every complex source with nonzero selected gap. There is no terminal
angle restriction, real-source assumption, or primitive supplied as input.
The single phase and the full beta data use the same normalized psi family. -/
theorem exists_sourceAngularEta_theorem13_1_ii
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen B ∧ realTypeSourceLocus p ⊆ B ∧ B ⊆ W₀ ∧
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        ∀ m : ℤ,
          IsOpen {ψ : CoeffPair p | ψ ∈ W ∧
            canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0} ∧
          AnalyticOnNhd ℂ (sourceAngularEtaAnalyticPhase hp hp1 m s)
            {ψ : CoeffPair p | ψ ∈ W ∧
              canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0} ∧
          (∀ ψ ∈ W, canonicalPeriodicGap hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0 →
              sourceAngularEtaAnalyticPhase hp hp1 m s ψ ≠ 0) ∧
          ∀ φ ∈ W, canonicalPeriodicGap hp hp1
            (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0 →
            ∃ V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
              ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
                φ ∈ U ∧ U ⊆ W ∧
                δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m/2 ∧
                SourceAngularEtaAnalyticChartData hp hp1 m s B V U c T r R z₀ ρ δ ε := by
  obtain ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,hW,hWreal,hWB,s,D,hcharts⟩ :=
    exists_sourceAngular_eta_remainder_cauchy_common_domain hp hp1
  have hlocal (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ)
      (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
      ∃ V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
        ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
          φ ∈ U ∧ U ⊆ W ∧
          δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m/2 ∧
          SourceAngularEtaAnalyticChartData hp hp1 m s B V U c T r R z₀ ρ δ ε := by
    obtain ⟨V,c,T,r,R,z₀,ρ,hφV,hVW,hrρ,hρR,C,_⟩ := hcharts φ hφ m
    obtain ⟨hO,hP⟩ := sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric hp hp1
      V C.source_open (fun ψ hψ => D.symmetric_analytic ψ (C.source_subset hψ)) m
    obtain ⟨U,δ,ε,hφU,hbase,E⟩ := C.exists_local_analytic_eta_chart ρ hrρ hρR φ hφV hgap
      (D.symmetric_analytic φ (hWB hφ) m).1 (D.symmetric_analytic φ (hWB hφ) m).2
      ((D.roots_analytic .dirichlet m).mono C.source_subset) hO hP
    exact ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,E.angle.source_subset.trans hVW,hbase,E⟩
  refine ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,hW,hWreal,hWB,s,D,?_⟩
  intro m
  refine ⟨?_,?_,?_,fun φ hφ hgap => hlocal φ hφ m hgap⟩
  · apply isOpen_iff_mem_nhds.mpr
    intro φ hφ
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,E⟩ := hlocal φ hφ.1 m hφ.2
    exact mem_of_superset (E.angle.source_open.mem_nhds hφU)
      (fun ψ hψ => ⟨hUW hψ,E.gap_ne_zero ψ hψ⟩)
  · intro φ hφ
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,E⟩ := hlocal φ hφ.1 m hφ.2
    exact E.analyticOnNhd_phase φ hφU
  · intro φ hφ hgap
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,E⟩ := hlocal φ hφ m hgap
    exact E.phase_ne_zero φ hφU

end NLS.ZakharovShabat
