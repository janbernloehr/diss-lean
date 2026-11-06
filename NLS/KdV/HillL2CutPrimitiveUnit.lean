import NLS.KdV.HillL2CutSquareDeflation
import NLS.ComplexAnalysis.RealTwoZeroUnit

/-! # The actual shifted Hill primitive as endpoint root times unit root

An analytic root of the deflated primitive-square unit is adjusted by
one constant sign on the connected cut domain. This gives the actual
shifted primitive, not just an arbitrary square root of its square.
-/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.exists_unit_root
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)) ∧
      (∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8), H z ≠ 0 ∧
        H z^2 = twoZeroQuotient (hillL2CutPrimitiveSquare n p.left p.right F) p.left p.right z) ∧
      ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
        F z+I*(n : ℂ)*Real.pi = endpointRoot p.left p.right z*H z := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  let Q := twoZeroQuotient X p.left p.right
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  let U := Ω \ segment ℝ (p.left : ℂ) p.right
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hQ,hfactor,hunit⟩ := h.square_deflated_unit q hq hreal n hn hcut p hopen R F
  obtain ⟨H,hH,hHsq⟩ := exists_analytic_squareRoot_on_ball Q _ (7*(n : ℝ)/8)
    (by positivity) hQ hunit
  let B : ℂ → ℂ := fun z => endpointRoot p.left p.right z*H z
  have hB : AnalyticOnNhd ℂ B U := by
    intro z hz
    exact (analyticOnNhd_endpointRoot _ _ z hz.2).mul (hH z hz.1)
  have hBsq (z : ℂ) (hz : z ∈ U) : B z^2 = X z := by
    dsimp only [B]
    rw [mul_pow,endpointRoot_sq _ _ z hz.2,(hHsq z hz.1).2]
    exact (hfactor z).symm
  have hBne (z : ℂ) (hz : z ∈ U) : B z ≠ 0 := by
    intro he
    have hx : X z = 0 := by rw [← hBsq z hz,he]; simp
    rcases (h.square_zero_iff q hq hreal n hn hcut p hopen R F z hz.1).mp hx with he | he
    · exact hz.2 (he ▸ left_mem_segment ℝ _ _)
    · exact hz.2 (he ▸ right_mem_segment ℝ _ _)
  have hloc := p.localization q hq n (by omega) hcut
  have hl : (p.left : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hconn : IsPreconnected U :=
    (isPathConnected_convex_complex_segment_complement_including_singleton
      Ω p.left p.right isOpen_ball (convex_ball _ _) hl).isConnected.isPreconnected
  have hm := (h.square_extension q hq hreal n hn hcut p hopen R F).2.1
  obtain ⟨k,hk,hmatch⟩ := exists_fixed_sign_of_sq_eq_on_preconnected
    (fun z => F z+I*(n : ℂ)*Real.pi) B U hconn
    (h.analytic.continuousOn.add continuousOn_const) hB.continuousOn
    (fun z hz => (hm hz).symm.trans (hBsq z hz).symm) hBne
  have hk2 : k^2 = 1 := by rcases hk with rfl | rfl <;> norm_num
  have hkne : k ≠ 0 := by rcases hk with rfl | rfl <;> norm_num
  refine ⟨fun z => k*H z,analyticOnNhd_const.mul hH,?_,?_⟩
  · intro z hz
    refine ⟨mul_ne_zero hkne (hHsq z hz).1,?_⟩
    rw [mul_pow,hk2,one_mul,(hHsq z hz).2]
  · intro z hz
    rw [hmatch z hz]
    dsimp only [B]
    ring

end NLS.KdV
