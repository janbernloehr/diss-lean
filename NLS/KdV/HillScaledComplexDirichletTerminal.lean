import NLS.KdV.HillComplexDirichletTerminal

/-! # Analytic Dirichlet terminal factors on arbitrarily small high-gap charts

A prescribed positive fraction of the free collar controls both the actual
Dirichlet root and the terminal factor, uniformly over bounded complex sources.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillScaledComplexDirichletGapTerminal (ρ : ℝ) (k : ℕ) (p : Coeff 2) : ℂ :=
  hillDirichletSheetRoot p (hillScaledDirichletRoot h0q h0r ρ k p)/
    hillFilledFreeGapRoot h0q h0r k (hillScaledDirichletRoot h0q h0r ρ k p,p)

theorem exists_hillScaledComplexDirichletGapTerminal_analytic_bound
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillScaledComplexDirichletGapTerminal h0q h0r ρ k) (ball (0 : Coeff 2) B) ∧
      ∀ p ∈ ball (0 : Coeff 2) B,
        hillScaledComplexDirichletGapTerminal h0q h0r ρ k p^2=
          hillLocalGapPolynomial 0 h0q h0r k p (hillScaledDirichletRoot h0q h0r ρ k p) ∧
        ‖hillScaledComplexDirichletGapTerminal h0q h0r ρ k p‖ ≤
          2*ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  obtain ⟨Nm,hNm,hmu⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r ρ hρ hρ1 B
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Nf,hNf,hfactor⟩ := exists_hillFilledFreeGapUnit_bounded_complex_factorization h0q h0r B
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r ρ hρ hρ1 B
  refine ⟨max (max Nm Nr) (max Nf Np),hNm.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro k hk
  have hkm : Nm ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkr : Nr ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hkf : Nf ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkp : Np ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNm.trans hkm
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let μ := hillScaledDirichletRoot h0q h0r ρ k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) : ‖p‖ ≤ B :=
    (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
  have hμK (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) : μ p ∈ closedBall c R :=
    closedBall_subset_closedBall (mul_le_of_le_one_left hR.le hρ1)
      (ball_subset_closedBall (((hmu k hkm).2 p (hpB p hp)).1))
  have hRn (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) : hillFilledFreeGapRoot h0q h0r k (μ p,p)≠0 :=
    ((hroot k hkr).2 p hp (μ p) (hμK p hp)).2.1
  have hma := (hmu k hkm).1
  refine ⟨?_,?_⟩
  · intro p hp
    have hpair : AnalyticAt ℂ (fun a : Coeff 2 => (μ a,a)) p := (hma p hp).prod analyticAt_id
    have hs := (analyticOnNhd_hillDirichletSheetRoot_joint (μ p,p) (mem_univ _)).comp
      (f := fun a : Coeff 2 => (μ a,a)) hpair
    have hr := ((hroot k hkr).1 (μ p,p) ⟨hμK p hp,hp⟩).comp
      (f := fun a : Coeff 2 => (μ a,a)) hpair
    exact hs.div hr (hRn p hp)
  · intro p hp
    have hzero := ((hmu k hkm).2 p (hpB p hp)).2.1
    have hsquare : hillScaledComplexDirichletGapTerminal h0q h0r ρ k p^2=hillLocalGapPolynomial 0 h0q h0r k p (μ p) := by
      rw [hillScaledComplexDirichletGapTerminal,div_pow,hillDirichletSheetRoot_sq_of_characteristic_zero p (μ p) hzero,
        hfactor p (hpB p hp) k hkf (μ p),← ((hroot k hkr).2 p hp (μ p) (hμK p hp)).1]
      exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (hRn p hp))
    refine ⟨hsquare,?_⟩
    obtain ⟨hboundary,a,ha,b,hb,haz,hbz,hm⟩ := hpairs p (hpB p hp) k hkp
    have haB : a ∈ ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) ha
    have hbB : b ∈ ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) hb
    have hmud : ‖μ p-c‖ ≤ ρ*R := by
      have hh := ((hmu k hkm).2 p (hpB p hp)).1
      have hh' : ‖μ p-c‖ < ρ*R := by simpa only [mem_ball,dist_eq_norm] using hh
      linarith
    have had : ‖a-c‖ ≤ ρ*R := by
      have hh : ‖a-c‖ < ρ*R := by simpa only [mem_ball,dist_eq_norm] using ha
      linarith
    have hbd : ‖b-c‖ ≤ ρ*R := by
      have hh : ‖b-c‖ < ρ*R := by simpa only [mem_ball,dist_eq_norm] using hb
      linarith
    have hma' : ‖μ p-a‖ ≤ 2*ρ*R := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (μ p) c a
      rw [norm_sub_rev c a] at hh
      linarith
    have hmb' : ‖μ p-b‖ ≤ 2*ρ*R := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (μ p) c b
      rw [norm_sub_rev c b] at hh
      linarith
    have he : ‖hillScaledComplexDirichletGapTerminal h0q h0r ρ k p‖^2=‖μ p-a‖*‖μ p-b‖ := by
      rw [← norm_pow,hsquare,hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk1 p hboundary haB hbB hm,norm_mul]
    have hh := mul_le_mul hma' hmb' (norm_nonneg _) (by positivity : 0 ≤ 2*ρ*R)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*ρ*R)).mp
    rw [he]
    simpa only [pow_two] using hh

end NLS.KdV
