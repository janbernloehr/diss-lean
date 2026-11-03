import NLS.KdV.HillAbelianComplexPeriods
import NLS.KdV.HillGlobalNormalizedDifferentials

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillBaseNormalizedComplexPsi (n : ℕ) (t : Coeff 2 × Coeff 2) (E : ℂ) : ℂ :=
  hillAbelianHilbertPsi n (E,t.1)/hillAbelianComplexPeriod q hq hr n n t

theorem analyticAt_hillAbelianComplexPeriod_general_root_germ
    (n k : ℕ) (hk : 1 ≤ k) (a : Coeff 2 → Coeff 2)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q)) :
    AnalyticAt ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a p,p))
      (SpectralWeight.one.toCoeff q) := by
  obtain ⟨U,_,hqU,hA⟩ := exists_hillAbelianComplexPeriod_analytic_neighborhood q hq hr n k hk
  exact (hA (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
    (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)

theorem analyticAt_hillBaseNormalizedComplexPsi_root_germ
    (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2 → Coeff 2)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q))
    (hne : hillAbelianHilbertPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q)) ≠ 0) (E : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a t.2,t.2) t.1)
      (E,SpectralWeight.one.toCoeff q) := by
  have hJ : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => (t.1,a t.2)) (E,SpectralWeight.one.toCoeff q) :=
    analyticAt_fst.prod (ha.comp (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd)
  have hN : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillAbelianHilbertPsi n (t.1,a t.2))
      (E,SpectralWeight.one.toCoeff q) := by
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a (SpectralWeight.one.toCoeff q)) (mem_univ _)).comp
      (f := fun t : ℂ × Coeff 2 => (t.1,a t.2)) hJ
  have hD : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillAbelianComplexPeriod q hq hr n n (a t.2,t.2))
      (E,SpectralWeight.one.toCoeff q) := by
    convert! (analyticAt_hillAbelianComplexPeriod_general_root_germ q hq hr n n hn a ha).comp
      (f := fun t : ℂ × Coeff 2 => t.2) (analyticAt_snd (𝕜 := ℂ) (p := (E,SpectralWeight.one.toCoeff q))) using 1
  have hneq : hillAbelianComplexPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ≠ 0 := by
    rw [hillAbelianComplexPeriod_at_base q hq hr n n hn]
    exact hne
  exact hN.div hD hneq

theorem hillBaseNormalizedComplexPsi_at_physical_roots
    (n : ℕ) (hn : 1 ≤ n) (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (E : ℂ) :
    hillBaseNormalizedComplexPsi q hq hr n
      (hillGapRootHilbertCoordinates q hq hr roots hroots,SpectralWeight.one.toCoeff q) E =
        hillAbelianPsiCandidate roots n E/hillAbelianCandidatePeriod q hq hr roots n n := by
  rw [hillBaseNormalizedComplexPsi,hillAbelianComplexPeriod_at_base q hq hr n n hn,
    hillAbelianHilbertPeriod_eq_genuine_period]
  congr 1
  exact hillAbelianHilbertPsi_eq_genuine_candidate q hq hr roots hroots n E

end NLS.KdV
