import NLS.KdV.HillSpectralCartesianAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The finite original Cartesian head has bounded analytic charts and
one exact real matching neighborhood around every real source potential. -/
theorem exists_hillSpectralCartesian_finite_analytic_head
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) :
    ∃ δ ε : ℝ, ∃ Z : ℕ → Coeff 2 → ℂ, 0<δ ∧ 0<ε ∧
      (∀ n<N, AnalyticOnNhd ℂ (Z n) (ball (SpectralWeight.one.toCoeff q) δ) ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ‖Z n p‖≤‖Z n (SpectralWeight.one.toCoeff q)‖+1) ∧
      ∀ r : RealPeriodOneHillPotential, dist r (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)<ε →
        ∀ n<N, ∀ hn : 1≤n, Z n (SpectralWeight.one.toCoeff r.val)=
          hillSpectralCartesian r.val r.property.1 r.property.2 n hn := by
  let p0 := SpectralWeight.one.toCoeff q
  let q0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  have hcharts (n : ℕ) : ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z p0 ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q0, ∀ hn : 1≤n,
        Z (SpectralWeight.one.toCoeff r.val)=hillSpectralCartesian r.val r.property.1 r.property.2 n hn := by
    by_cases hn : 1≤n
    · obtain ⟨Z,hZa,hZr⟩ := exists_hillSpectralCartesian_analytic_extension h0q h0r q hq hr n hn
      refine ⟨Z,hZa,?_⟩
      filter_upwards [hZr] with r hrr
      exact fun _ => hrr
    · refine ⟨fun _ => 0,analyticAt_const,Filter.Eventually.of_forall ?_⟩
      intro r hn'
      exact (hn hn').elim
  choose Z hZa hZr using hcharts
  have hcomplex : ∀ᶠ p : Coeff 2 in 𝓝 p0, ∀ n∈Finset.range N,
      AnalyticAt ℂ (Z n) p ∧ ‖Z n p‖<‖Z n p0‖+1 := by
    apply (Filter.eventually_all_finset _).mpr
    intro n _
    filter_upwards [(isOpen_analyticAt ℂ (Z n)).mem_nhds (hZa n),
      (hZa n).continuousAt.norm.tendsto.eventually (isOpen_Iio.mem_nhds (by linarith : ‖Z n p0‖<‖Z n p0‖+1))] with p hpa hpb
    exact ⟨hpa,hpb⟩
  have hreal : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q0, ∀ n∈Finset.range N,
      ∀ hn : 1≤n, Z n (SpectralWeight.one.toCoeff r.val)=hillSpectralCartesian r.val r.property.1 r.property.2 n hn :=
    (Filter.eventually_all_finset _).mpr (fun n _ => hZr n)
  obtain ⟨δ,hδ,hδsrc⟩ := Metric.mem_nhds_iff.mp hcomplex
  obtain ⟨ε,hε,hεsrc⟩ := Metric.mem_nhds_iff.mp hreal
  refine ⟨δ,ε,Z,hδ,hε,?_,?_⟩
  · intro n hn
    refine ⟨(fun p hp => (hδsrc hp n (Finset.mem_range.mpr hn)).1),?_⟩
    intro p hp
    exact (hδsrc hp n (Finset.mem_range.mpr hn)).2.le
  · intro r hrr n hn hn'
    exact hεsrc (show r∈ball q0 ε from hrr) n (Finset.mem_range.mpr hn) hn'

end NLS.KdV
