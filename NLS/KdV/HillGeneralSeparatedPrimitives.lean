import NLS.KdV.HillActiveRegularAnnulus
import NLS.KdV.HillUniformPointwiseQuadraticSolution
import NLS.KdV.HillGeneralHighContourCharts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Common analytic quadratic primitives for the actual normalized
physical differentials. The source ball, cutoff and kernel constant all
precede the differential index, and every off-diagonal high gap is kept. -/
theorem exists_hillSelectedPsi_general_separated_quadratic_primitives :
    ∃ δ L S : ℝ, ∃ N : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<L ∧ 0<S ∧ 1≤N ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 L ∧
      IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ k : ℕ, N≤k → k≠n → ∃ H : ℂ × Coeff 2 → ℂ,
          AnalyticOnNhd ℂ H (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
            (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4) ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
          (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ E∈ball (hillRealGapCenter 0 h0q h0r k : ℂ)
            (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
            hillLocalGapPolynomial 0 h0q h0r k p E*deriv (fun z => H (z,p)) E+
              (E-hillLocalGapMidpoint 0 h0q h0r k p)*H (E,p)=hillComplexRegularGapNumerator h0q h0r G k (E,p)) ∧
          ∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
            ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
            ‖H (E,p)‖≤36*Real.pi*S*hillOffDiagonalPeriodKernel n (k : ℤ)) ∧
        ∀ p∈V, ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E := by
  obtain ⟨δ,S,L,J,V,hδ,hS,hL,hJ,hsub,hV,hqV,hsource,hcharts⟩ :=
    exists_hillSelectedPsi_uniform_general_high_contour_charts q hq hr h0q h0r
  let U : Set (Coeff 2) := ball (SpectralWeight.one.toCoeff q) δ
  obtain ⟨Na,hNa,hannulus⟩ := exists_hillRegularGapDensity_uniform_active_zero_periods h0q h0r U L hsub
  obtain ⟨Nb,hNb,hbounds⟩ := exists_hillRegularGapDensity_uniform_active_contour_bounds h0q h0r U L hsub
  obtain ⟨Nq,hNq,hquadratic⟩ := exists_hillRegularGap_uniform_pointwise_quadratic_solution h0q h0r L
  let N := max J (max Na (max Nb Nq))
  have hN : 1≤N := hJ.trans (le_max_left _ _)
  refine ⟨δ,L,S,N,V,hδ,hL,hS,hN,hsub,hV,hqV,hsource,?_⟩
  intro n hn
  obtain ⟨G,hGa,hreal,hdata⟩ := hcharts n hn
  let b : ℕ → ℝ := fun k => S*hillOffDiagonalPeriodKernel n (k : ℤ)
  have hb (k : ℕ) : 0≤b k := mul_nonneg hS.le (hillOffDiagonalPeriodKernel_nonneg n (k : ℤ))
  have hz : ∀ p∈U, ∀ k : ℕ, 1≤k → (J≤k ∧ k≠n) →
      (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
        hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))=0 := by
    intro p hp k hk hactive
    have hh := (hdata p hp k hactive.1).2
    rw [if_neg hactive.2] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hB : ∀ p∈U, ∀ k : ℕ, 1≤k → (J≤k ∧ k≠n) → ∀ E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤b k :=
    fun p hp k hk hactive E hE => ((hdata p hp k hactive.1).1 E hE).2.2 hactive.2
  refine ⟨G,hGa,?_,hreal⟩
  intro k hk hkn
  have hka : Na≤k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkb : Nb≤k := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hk))
  have hkq : Nq≤k := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hk))
  have hk1 : 1≤k := hN.trans hk
  have hk0 : (k : ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  have hactive : J≤k ∧ k≠n := ⟨(le_max_left _ _).trans hk,hkn⟩
  obtain ⟨hg,hD,hann⟩ := hannulus G hGa (fun k => J≤k ∧ k≠n) hz k hka hactive
  have hbd := hbounds G hGa b hb (fun k => J≤k ∧ k≠n) hB k hkb hactive
  let C : ℝ := (k : ℝ)^3*b k
  have hC : 0≤C := mul_nonneg (pow_nonneg (Nat.cast_nonneg k) 3) (hb k)
  have hchart : HillRegularGapAnalyticChart h0q h0r G U k C := by
    refine ⟨hg,hD,?_⟩
    intro p hp
    obtain ⟨hpoint,houter,hinner⟩ := hann p hp
    obtain ⟨hdisc,hcircle⟩ := hbd p hp
    refine ⟨hpoint,houter,hinner,?_,?_⟩
    · intro E hE
      apply (hdisc E hE).trans_eq
      dsimp only [C]
      field_simp
    · intro E hE
      apply (hcircle E hE).trans_eq
      dsimp only [C]
      field_simp
  obtain ⟨H,hHa,hODE,hHb⟩ := hquadratic U isOpen_ball hsub G k hkq C hC hchart
  refine ⟨H,hHa,hODE,?_⟩
  intro p hp E hE
  apply (hHb p hp E hE).trans_eq
  dsimp only [C,b]
  field_simp

end NLS.KdV
