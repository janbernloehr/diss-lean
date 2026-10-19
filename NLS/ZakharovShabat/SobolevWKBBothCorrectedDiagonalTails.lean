import NLS.ZakharovShabat.SobolevWKBFirstCorrectedDiagonalTail
import NLS.SequenceSpaces.Reflection

/-! # Both full corrected diagonal remainders

Signed swap symmetry gives a common H^(N+1) tail bound for both corrected diagonal remainders at every larger cutoff.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The second diagonal remainder is exactly the first remainder for
the signed swapped potential and reflected spectral parameter. -/
theorem nlsWKBSecondRemainder_snd_eq
    (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (N : ℕ) (z : ℂ) (t : Icc (0:ℝ) 1) :
    (nlsWKBSecondRemainder a b ha hb N z t).2 =
      (nlsWKBFirstRemainder (-b) (-a) hb.neg ha.neg N (-z) t).1 := by
  have hd := classicalSolution_swap (classicalPotentialOfFunctions a b ha hb)
    z (nlsWKBVector (-b) (-a) N (-z) 0) t
  rw [classicalSwapPotential_ofFunctions] at hd
  change classicalSolution (classicalPotentialOfFunctions a b ha hb) z
    (nlsWKBSecondVector a b N z 0) t = _ at hd
  unfold nlsWKBSecondRemainder nlsWKBFirstRemainder
  rw [hd]
  rfl

/-- Both full diagonal WKB remainders, after removing their explicit
phase primitives, have H^(N+1) tails on the
original Hs ball for 1 <= N <= s. A single cutoff and norm bound work
for both columns, all physical times, and the same displacement budgets. -/
theorem exists_uniform_nlsWKB_both_corrected_diagonal_tail_bound
    (s N : ℕ) (hN : 1 ≤ N) (hNs : N ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ t : Icc (0:ℝ) 1,
      ∃ f g : ScalarSobolev (N+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          (nlsWKBFirstRemainder a b ha.continuous hb.continuous N ((Real.pi:ℂ)*n+δ n) t).1-
            nlsWKBDiagonalPhasePrimitive a b N ((Real.pi:ℂ)*n+δ n) t
          else 0) ∧
        (∀ n, g.val n = if K' ≤ n.natAbs then
          (nlsWKBSecondRemainder a b ha.continuous hb.continuous N ((Real.pi:ℂ)*n+δ n) t).2-
            nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-((Real.pi:ℂ)*n+δ n)) t
          else 0) ∧ ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_first_corrected_diagonal_tail_bound s N hN hNs R D M hR hD
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM t
  obtain ⟨f,hf,hfn⟩ := h K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM t
  let cd : SobolevSource s := (-ab.2,-ab.1)
  have hcd : ‖cd‖ ≤ R := by simpa only [cd,Prod.norm_def,norm_neg,max_comm] using hab
  have hc1 (j : ℤ) : cd.1.val j = periodOneCoefficient (-b) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
  have hc2 (j : ℤ) : cd.2.val j = periodOneCoefficient (-a) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
  let δ' : NLS.Coeff ⊤ := -Coeff.reflection δ
  have hδ'D : ‖δ'‖ ≤ D := by simpa only [δ',norm_neg,LinearIsometryEquiv.norm_map] using hδD
  have hδ'M (n : ℤ) : (1+|(n:ℝ)|)*‖δ' n‖ ≤ M := by
    change (1+|(n:ℝ)|)*‖-δ (-n)‖ ≤ M
    simpa only [norm_neg,Int.cast_neg,abs_neg] using hδM (-n)
  obtain ⟨g,hg,hgn⟩ := h K' hK' cd hcd (-b) (-a) hb.neg ha.neg
    (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hc1 hc2 δ' hδ'D hδ'M t
  refine ⟨f,WeightedCoeff.reflection ((N+1:ℕ):ℝ) g,hf,?_,hfn,?_⟩
  · intro n
    rw [WeightedCoeff.reflection_apply,hg (-n),Int.natAbs_neg]
    split_ifs with hn
    · have hz : (Real.pi:ℂ)*(-n)+δ' (-n) = -((Real.pi:ℂ)*n+δ n) := by
        change (Real.pi:ℂ)*(-n)-δ (-(-n)) = -((Real.pi:ℂ)*n+δ n)
        simp only [neg_neg]
        ring
      simp only [Int.cast_neg]
      rw [hz,nlsWKBSecondRemainder_snd_eq]
    · rfl
  · simpa only [LinearIsometryEquiv.norm_map] using hgn

end NLS.ZakharovShabat
