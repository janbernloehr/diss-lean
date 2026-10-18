import NLS.ZakharovShabat.ClassicalSwapSymmetry
import NLS.ZakharovShabat.SobolevWKBLeadingOscillatoryComparison

/-! # The second WKB vector and its leading oscillatory error

The second solution has the same uniform extra-order remainder on original Sobolev balls and horizontal strips.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The exact leading scalar oscillatory integral in the WKB error. -/
def nlsWKBLeadingTerm (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  -I*((2*I*z)⁻¹)^N*exp (I*z*t)*
    (∫ x in (0:ℝ)..t, nlsRiccatiDensity a b N x*exp (-2*I*z*x))

/-- The second WKB vector uses the signed swap and reflected spectral parameter. -/
def nlsWKBSecondVector (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ × ℂ :=
  (nlsWKBVector (-b) (-a) N (-z) t).swap

/-- The second actual solution column has an explicit leading oscillatory
correction with the same source regularity and uniform extra-order error. -/
theorem exists_uniform_nlsWKB_second_leading_oscillatory_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖nlsWKBSecondVector a b N z t-
          classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
            (nlsWKBSecondVector a b N z 0) t-
          (nlsWKBLeadingTerm (-b) (-a) N (-z) t.val,0)‖ ≤
            C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_nlsWKB_leading_oscillatory_error_bound s N hs hNs R hR H
  refine ⟨C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH t
  let cd : SobolevSource s := (-ab.2,-ab.1)
  have hcd : ‖cd‖ ≤ R := by simpa only [cd,Prod.norm_def,norm_neg,max_comm] using hab
  have hc1 (j : ℤ) : cd.1.val j = periodOneCoefficient (-b) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
  have hc2 (j : ℤ) : cd.2.val j = periodOneCoefficient (-a) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
  have hh := h cd hcd (-b) (-a) hb.neg ha.neg (by intro x; change -b (x+1) = -b x; rw [hpb x])
    (by intro x; change -a (x+1) = -a x; rw [hpa x]) hc1 hc2
    (-z) (by simpa using hzn) (by simpa using hzH) t
  have hd := classicalSolution_swap (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
    z (nlsWKBVector (-b) (-a) N (-z) 0) t
  rw [classicalSwapPotential_ofFunctions] at hd
  change classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
    (nlsWKBSecondVector a b N z 0) t = _ at hd
  rw [hd]
  have hn : ‖(2*I*(-z))⁻¹‖ = ‖(2*I*z)⁻¹‖ := by simp only [mul_neg,inv_neg,norm_neg]
  rw [hn] at hh
  simpa only [nlsWKBSecondVector,nlsWKBLeadingTerm,Prod.norm_def,
    Prod.fst_sub,Prod.snd_sub,Prod.fst_swap,Prod.snd_swap,Prod.fst,Prod.snd,max_comm] using hh

end NLS.ZakharovShabat
