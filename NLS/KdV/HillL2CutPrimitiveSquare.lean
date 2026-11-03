import NLS.KdV.HillL2CutEndpointNormalization
import NLS.ComplexAnalysis.GapPrimitiveSquare

/-! # Analytic squares of the actual shifted Hill cut primitives

The exact endpoint normalization lets the existing shared gap-square
extension fill the entire real cut. The full deflated unit absorbs the
nonquadratic part of the actual characteristic into an analytic numerator.
-/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

def hillL2CutPrimitiveSquare (n : ℕ) (l u : ℝ) (F : ℂ → ℂ) : ℂ → ℂ :=
  gapPrimitiveSquareExtension (fun z => F z+I*(n : ℂ)*Real.pi) l u

theorem HillL2NormalizedCutPrimitive.square_extension
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    AnalyticOnNhd ℂ (hillL2CutPrimitiveSquare n p.left p.right F)
      (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)) ∧
    EqOn (hillL2CutPrimitiveSquare n p.left p.right F) (fun z => (F z+I*(n : ℂ)*Real.pi)^2)
      (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right) ∧
    hillL2CutPrimitiveSquare n p.left p.right F p.left = 0 ∧
    hillL2CutPrimitiveSquare n p.left p.right F p.right = 0 := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let Q := twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  let U := Ω \ segment ℝ (p.left : ℂ) p.right
  obtain ⟨hQ,hfactor,hunit⟩ := p.deflated_unit q n hn1
  obtain ⟨V,hV,hVsq⟩ := exists_analytic_squareRoot_on_ball Q (freeHillValue n : ℂ) (n : ℝ)
    hnpos (hQ.mono ball_subset_closedBall) (fun z hz => hunit z (ball_subset_closedBall hz))
  have hsub : Ω ⊆ ball (freeHillValue n : ℂ) (n : ℝ) := ball_subset_ball (by linarith)
  have hUsub : U ⊆ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right :=
    fun z hz => ⟨hsub hz.1,hz.2⟩
  let S : ℂ → ℂ := fun z => R z/V z
  let g : ℂ → ℂ := fun z => deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z/V z
  have hg : AnalyticOnNhd ℂ g Ω :=
    ((analyticOnNhd_hillL2Discriminant _).deriv.mono (subset_univ _)).div
      (hV.mono hsub) (fun z hz => (hVsq z (hsub hz)).1)
  have hS : ContinuousOn S U :=
    (h.root_analytic.mono hUsub).continuousOn.div (hV.mono (fun z hz => hsub hz.1)).continuousOn
      (fun z hz => (hVsq z (hsub hz.1)).1)
  have hsq (z : ℂ) (hz : z ∈ U) : S z^2 = (p.left-z)*(p.right-z) := by
    dsimp only [S]
    rw [div_pow,(h.root_data z (hUsub hz)).2,(hVsq z (hsub hz.1)).2,hfactor z]
    change (z-p.left)*(z-p.right)*Q z/Q z = _
    rw [mul_div_cancel_right₀ _ (hunit z (ball_subset_closedBall (hsub hz.1)))]
    ring
  have hd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (fun w => F w+I*(n : ℂ)*Real.pi) (g z/S z) z := by
    convert! (h.hasDerivAt z hz).add_const (I*(n : ℂ)*Real.pi) using 1
    dsimp only [g,S]
    field_simp [(hVsq z (hsub hz.1)).1,(h.root_data z (hUsub hz)).1]
  have hloc := p.localization q hq n hn1 (by linarith [norm_nonneg q])
  have hl : (p.left : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hr : (p.right : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.2]
  have ht := h.shifted_endpoint_normalization q hq hreal n hn hcut p hopen R F
  exact gapPrimitiveSquareExtension_spec g S _ Ω p.left p.right isOpen_ball
    ((convex_ball _ _).segment_subset hl hr) hg hS hsq hd ht.1 ht.2

theorem HillL2NormalizedCutPrimitive.square_conj
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8),
      hillL2CutPrimitiveSquare n p.left p.right F (conj z) =
        conj (hillL2CutPrimitiveSquare n p.left p.right F z) := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  obtain ⟨hX,hm,_,_⟩ := h.square_extension q hq hreal n hn hcut p hopen R F
  have hc (z : ℂ) (hz : z ∈ Ω) : conj z ∈ Ω := by
    simpa only [Ω,mem_ball,dist_conj_comm,conj_ofReal] using hz
  apply continuous_eqOn_of_dense_on_open (segment ℝ (p.left : ℂ) p.right)ᶜ Ω
    (dense_complex_segment_complement _ _) isOpen_ball (fun z => X (conj z)) (fun z => conj (X z))
    (hX.continuousOn.comp continuous_conj.continuousOn hc)
    (continuous_conj.comp_continuousOn hX.continuousOn)
  intro z hz
  dsimp only [X]
  rw [hm (conj_mem_real_cut _ _ _ _ z hz),hm hz]
  dsimp only
  rw [(h.reflection q hq hreal n (by omega) hcut p R F z hz).2,map_pow,map_add]
  simp only [map_mul,conj_I,map_natCast,conj_ofReal]
  ring

theorem HillL2NormalizedCutPrimitive.square_im_eq_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (x : ℝ) (hx : (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)) :
    (hillL2CutPrimitiveSquare n p.left p.right F x).im = 0 := by
  have he := congrArg Complex.im (h.square_conj q hq hreal n hn hcut p hopen R F x hx)
  simp only [conj_ofReal,conj_im] at he
  linarith

end NLS.KdV
