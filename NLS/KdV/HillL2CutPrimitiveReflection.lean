import NLS.KdV.HillL2NormalizedCutPrimitive
import NLS.KdV.HillL2PrimitiveReflection
import NLS.ComplexAnalysis.RealCutConjugation

/-! # Reflection on the full local Hill cut

The free-sheet reflection sign extends from the source circle to the
entire connected cut domain. In particular the normalized primitive is
purely imaginary at every real point of this domain.
-/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.reflection
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
      R (conj z) = -conj (R z) ∧ F (conj z) = -conj (F z) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let A := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right
  let a : ℂ := (freeHillValue n : ℂ) + (3*(n : ℝ)/4 : ℝ)
  have ha : a ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    simp only [a,mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 3*(n : ℝ)/4)]
  have hloc := p.localization q hq n hn hcut
  have hL : (p.left : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hseg : segment ℝ (p.left : ℂ) p.right ⊆ closedBall (freeHillValue n : ℂ) (4*‖q‖) := by
    apply (convex_closedBall _ _).segment_subset
    · simpa only [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hloc.1
    · simpa only [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hloc.2
  have haA : a ∈ A := by
    have he : ‖a-(freeHillValue n : ℂ)‖ = 3*(n : ℝ)/4 := by
      simpa only [mem_sphere,dist_eq_norm] using ha
    refine ⟨?_,?_⟩
    · rw [mem_ball,dist_eq_norm,he]; linarith
    · intro hs
      have hb := hseg hs
      rw [mem_closedBall,dist_eq_norm,he] at hb
      linarith
  have hsub : A ⊆ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right := by
    intro z hz
    exact ⟨ball_subset_ball (by linarith) hz.1,hz.2⟩
  have hconn : IsPreconnected A :=
    (isPathConnected_convex_complex_segment_complement_including_singleton
      _ p.left p.right isOpen_ball (convex_ball _ _) hL).isConnected.isPreconnected
  have hasrc : (a,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    apply mem_hillL2ContinuationDomain_of_high_distance q hq n hn hcut a
      (ball_subset_closedBall (hsub haA).1)
    have he : ‖a-(freeHillValue n : ℂ)‖ = 3*(n : ℝ)/4 := by
      simpa only [mem_sphere,dist_eq_norm] using ha
    rw [he]; linarith
  have hac : conj a = a := by simp only [a,map_add,conj_ofReal]
  apply traceRoot_primitive_reflection _ R F A hconn
    (conj_mem_real_cut _ _ _ _) (fun z _ => hillL2Discriminant_conj _ hreal z)
    (h.root_analytic.mono hsub).continuousOn h.analytic.continuousOn
    (fun z hz => (h.root_data z (hsub hz)).2) (fun z hz => (h.root_data z (hsub hz)).1)
    h.exp_eq a haA
  · rw [hac,h.root_source a ha]
    simpa only [hac] using hillL2ContinuedRoot_conj _ hreal a hasrc
  · rw [hac,h.source a ha]
    simpa only [hac] using hillL2ContinuedPrimitive_conj _ hreal a hasrc

theorem HillL2NormalizedCutPrimitive.re_eq_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (x : ℝ) (hx : (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right) :
    (F x).re = 0 := by
  have he := congrArg Complex.re (h.reflection q hq hreal n hn hcut p R F x hx).2
  simp only [conj_ofReal,neg_re,conj_re] at he
  linarith

end NLS.KdV
