import NLS.KdV.HillL2NormalizedCutPrimitive
import NLS.KdV.HillL2GapCutBoundary

/-! # Algebraic values of the finite Hill primitive endpoint limits

The normalized primitive has finite limits at an open pair. Their
exponentials are half the actual endpoint traces, their hyperbolic
sines vanish, and the cut root tends to zero. Selecting the exact
integer multiple of `π i` and proving the gap jump remain separate.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.endpoint_values
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    ∃ A B : ℂ,
      Tendsto F (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.left) (𝓝 A) ∧
      Tendsto F (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.right) (𝓝 B) ∧
      exp A = hillL2Discriminant (SpectralWeight.one.toCoeff q) p.left/2 ∧
      exp B = hillL2Discriminant (SpectralWeight.one.toCoeff q) p.right/2 ∧
      2*cosh A = hillL2Discriminant (SpectralWeight.one.toCoeff q) p.left ∧
      2*cosh B = hillL2Discriminant (SpectralWeight.one.toCoeff q) p.right ∧
      sinh A = 0 ∧ sinh B = 0 ∧
      Tendsto R (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.left) (𝓝 0) ∧
      Tendsto R (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.right) (𝓝 0) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  let U := Ω \ segment ℝ (p.left : ℂ) p.right
  have hsub : U ⊆ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right := by
    intro z hz
    exact ⟨ball_subset_ball (by linarith) hz.1,hz.2⟩
  have hloc := p.localization q hq n hn (by linarith [norm_nonneg q])
  have hl : (p.left : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hr : (p.right : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.2]
  have : NeBot (𝓝[U] (p.left : ℂ)) := mem_closure_iff_nhdsWithin_neBot.mp
    ((dense_complex_segment_complement (p.left : ℂ) p.right).open_subset_closure_inter isOpen_ball hl)
  have : NeBot (𝓝[U] (p.right : ℂ)) := mem_closure_iff_nhdsWithin_neBot.mp
    ((dense_complex_segment_complement (p.left : ℂ) p.right).open_subset_closure_inter isOpen_ball hr)
  obtain ⟨A,B,hA,hB⟩ := p.primitive_endpoint_limits q hq n hn hcut hopen R F
    h.root_analytic h.root_data h.hasDerivAt
  have hlzero : hillL2Discriminant (SpectralWeight.one.toCoeff q) p.left^2 = 4 :=
    sub_eq_zero.mp p.left_zero
  have hrzero : hillL2Discriminant (SpectralWeight.one.toCoeff q) p.right^2 = 4 :=
    sub_eq_zero.mp p.right_zero
  have ha := traceRoot_primitive_boundary_values _ R F U p.left A
    ((analyticOnNhd_hillL2Discriminant _ p.left (mem_univ _)).continuousAt) hlzero
    (fun z hz => (h.root_data z (hsub hz)).2) h.exp_eq hA
  have hb := traceRoot_primitive_boundary_values _ R F U p.right B
    ((analyticOnNhd_hillL2Discriminant _ p.right (mem_univ _)).continuousAt) hrzero
    (fun z hz => (h.root_data z (hsub hz)).2) h.exp_eq hB
  exact ⟨A,B,hA,hB,ha.1,hb.1,ha.2.1,hb.2.1,ha.2.2.1,hb.2.2.1,ha.2.2.2,hb.2.2.2⟩

end NLS.KdV
