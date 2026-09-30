import NLS.ComplexAnalysis.AnalyticFromSquare
import NLS.ZakharovShabat.SourceSymmetricContour
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-!
# Analytic canonical endpoints near an open real source gap

The symmetric contour invariants give the analytic midpoint and squared gap.
Continuity fixes the nonzero gap's square-root sign near a real source.
Consequently the gap and its two individually labeled endpoints are analytic,
including central indices. A local neighborhood can be confined to any given
open source domain and keeps the selected gap noncollapsed.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every nonzero canonical source gap is analytic at a real source. -/
theorem analyticAt_sourceCanonicalPeriodicGap_of_realType_nonzero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) φ := by
  obtain ⟨W,_,_,hWreal,hW⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hsquare := (hW φ (hWreal hreal) m).2
  have hcont : ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) φ :=
    (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hreal m).sub
      (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hreal m)
  exact analyticAt_of_analyticAt_sq_of_continuousAt _ φ hcont hsquare hgap

/-- Both individual canonical periodic endpoints are source analytic near
every real source at which their selected gap is open. -/
theorem analyticAt_sourceCanonicalPeriodicEndpoints_of_realType_nonzero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) φ ∧
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) φ := by
  obtain ⟨W,_,_,hWreal,hW⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hτ := (hW φ (hWreal hreal) m).1
  have hγ := analyticAt_sourceCanonicalPeriodicGap_of_realType_nonzero hp hp1 φ hreal m hgap
  constructor
  · convert hτ.sub (hγ.div_const (c := (2:ℂ))) using 1
    funext ψ
    dsimp [canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  · convert hτ.add (hγ.div_const (c := (2:ℂ))) using 1
    funext ψ
    dsimp [canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring

/-- One neighborhood inside a prescribed open domain makes the actual
midpoint and gap analytic and keeps the selected gap nonzero. -/
theorem exists_local_sourceCanonicalOpenGap_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (O : Set (CoeffPair p)) (hO : IsOpen O)
    (φ : CoeffPair p) (hφ : φ ∈ O) (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ O ∧
      AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) V ∧
      AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) V ∧
      ∀ ψ ∈ V, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0 := by
  obtain ⟨W,_,_,hWreal,hW⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hτ := (hW φ (hWreal hreal) m).1
  have hγ := analyticAt_sourceCanonicalPeriodicGap_of_realType_nonzero hp hp1 φ hreal m hgap
  have hOevent : ∀ᶠ ψ in 𝓝 φ, ψ ∈ O := hO.mem_nhds hφ
  have hgood := hOevent.and (hτ.eventually_analyticAt.and
    (hγ.eventually_analyticAt.and (hγ.continuousAt.eventually_ne hgap)))
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp hgood
  exact ⟨V,hV,hφV,(fun ψ hψ => (hVsub hψ).1),
    (fun ψ hψ => (hVsub hψ).2.1),(fun ψ hψ => (hVsub hψ).2.2.1),
    (fun ψ hψ => (hVsub hψ).2.2.2)⟩

end NLS.ZakharovShabat
