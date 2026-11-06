import NLS.KdV.HillUniformCenteredGapData
import NLS.KdV.HillUniformCenteredMeanFreePrimitives
import NLS.KdV.HillGeneralDeflatedDiscCharts
import NLS.ComplexAnalysis.BoundedCenteredMeanFreeQuadratic

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
/-- The actual normalized Hill differentials have common quantitative
centered mean-free quadratic primitives on every high gap, including
k=n. The source radius, cutoff and bound precede both indices. -/
theorem exists_hillSelectedPsi_general_centered_mean_free_primitives :
    ∃ δ L B : ℝ, ∃ N : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<L ∧ 0<B ∧ 1≤N ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 L ∧
      IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ k : ℕ, N≤k → ∃ Q : ℂ × Coeff 2 → ℂ,
          AnalyticOnNhd ℂ Q (ball (0:ℂ)
            ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4) ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
          (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ w∈ball (0:ℂ)
            ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
            (w^2-hillLocalGapSquare 0 h0q h0r k p/4)*deriv (fun z => Q (z,p)) w+w*Q (w,p)=
              centeredMeanFree (hillCenteredComplexRegularGapNumerator h0q h0r G k)
                (fun p => hillLocalGapSquare 0 h0q h0r k p/4) (w,p)) ∧
          ∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ w∈closedBall (0:ℂ)
            ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/8),
            ‖Q (w,p)‖≤64*Real.pi*B/(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) ∧
        ∀ p∈V, ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E := by
  obtain ⟨δ,L,B,Nf,V,hδ,hL,hB,hNf,hsub,hV,hqV,hsource,hcharts⟩ :=
    exists_hillSelectedPsi_general_uniform_deflated_disc_charts q hq hr h0q h0r
  obtain ⟨Nd,hNd,hdata⟩ := exists_hillLocalGap_bounded_centered_data h0q h0r (1/32) (by norm_num) (by norm_num) L
  let N := max Nf Nd
  have hN : 1≤N := hNf.trans (le_max_left _ _)
  refine ⟨δ,L,B,N,V,hδ,hL,hB,hN,hsub,hV,hqV,hsource,?_⟩
  intro n hn
  obtain ⟨G,hGa,hdiscs,hreal⟩ := hcharts n hn
  refine ⟨G,hGa,?_,hreal⟩
  intro k hk
  have hkF : Nf≤k := (le_max_left _ _).trans hk
  have hkD : Nd≤k := (le_max_right _ _).trans hk
  have hk1 : 1≤k := hN.trans hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let U : Set (Coeff 2) := ball (SpectralWeight.one.toCoeff q) δ
  let τ := hillLocalGapMidpoint 0 h0q h0r k
  let s : Coeff 2 → ℂ := fun p => hillLocalGapSquare 0 h0q h0r k p/4
  let f := hillCenteredComplexRegularGapNumerator h0q h0r G k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpδ (p : Coeff 2) (hp : p∈U) : ‖p‖≤L :=
    (show ‖p‖<L by simpa only [mem_ball,dist_zero_right] using hsub hp).le
  have hpos (w : ℂ) (hw : w∈closedBall (0:ℂ) (R/2)) (p : Coeff 2) (hp : p∈U) :
      τ p+w∈closedBall c R := by
    have ht := ((hdata k hkD).2.2 p (hpδ p hp)).1
    have hw' : ‖w‖≤R/2 := by simpa only [mem_closedBall,dist_zero_right] using hw
    rw [mem_closedBall,dist_eq_norm]
    have hh : ‖τ p+w-c‖≤‖τ p-c‖+‖w‖ := by
      rw [show τ p+w-c=(τ p-c)+w by ring]
      exact norm_add_le _ _
    linarith
  have hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) (R/2) ×ˢ U) := by
    intro t ht
    have hm := ((hdata k hkD).1 t.2 (hsub ht.2)).comp (f := fun u : ℂ × Coeff 2 => u.2) analyticAt_snd
    have hT : AnalyticAt ℂ (fun u : ℂ × Coeff 2 => (τ u.2+u.1,u.2)) t :=
      (hm.add analyticAt_fst).prod analyticAt_snd
    exact ((hdiscs k hkF).1 (τ t.2+t.1,t.2) ⟨hpos t.1 ht.1 t.2 ht.2,ht.2⟩).comp
      (f := fun u : ℂ × Coeff 2 => (τ u.2+u.1,u.2)) hT
  have hs : AnalyticOnNhd ℂ s U := (hdata k hkD).2.1.mono hsub
  have hsmall (p : Coeff 2) (hp : p∈U) : ‖s p‖<((R/2)/8)^2 := by
    have hh := ((hdata k hkD).2.2 p (hpδ p hp)).2
    nlinarith
  have hb (p : Coeff 2) (hp : p∈U) (w : ℂ) (hw : w∈closedBall (0:ℂ) (R/2)) : ‖f (w,p)‖≤B :=
    (hdiscs k hkF).2 p hp (τ p+w) (hpos w hw p hp)
  obtain ⟨Q,hQa,hODE,hQb⟩ := exists_bounded_analytic_centered_mean_free_quadratic_solution f s U isOpen_ball
    (R/2) B (by positivity) hB.le hf hs hsmall hb
  have hr2 : (R/2)/2=R/4 := by ring
  have hr4 : (R/2)/4=R/8 := by ring
  rw [hr2] at hQa hODE
  rw [hr4] at hQb
  refine ⟨Q,hQa,hODE,?_⟩
  intro p hp w hw
  apply (hQb p hp w hw).trans_eq
  change 32*Real.pi*B/(R/2)=64*Real.pi*B/R
  field_simp
  ring

end NLS.KdV
