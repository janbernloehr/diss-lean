import NLS.ZakharovShabat.SobolevWKBLeadingFourierTail
import NLS.SequenceSpaces.Reflection

/-! # Both original Fourier coefficients in the leading WKB integrals

A common cutoff and norm bound control the two leading-integral tails, with the exact signed first and second coefficients.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Both actual leading WKB integrals have the original signed Fourier
coefficients with H^(s+1) tail errors. A single cutoff and constant work
for both columns, on the original Sobolev ball and displacement budgets. -/
theorem exists_uniform_nlsWKB_both_leading_fourier_tail_error_bound
    (s : ℕ) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm a b s ((Real.pi:ℂ)*n+δ n) 1-
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧
        (∀ n, g.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm (-b) (-a) s (-((Real.pi:ℂ)*n+δ n)) 1+
            I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n) else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKBLeadingTerm_fourier_tail_error_bound s R D M hR hD hM
  refine ⟨K,hK,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  obtain ⟨f,hf,hfn⟩ := h ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
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
  obtain ⟨g,hg,hgn⟩ := h cd hcd (-b) (-a) hb.neg ha.neg
    (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hc1 hc2 δ' hδ'D hδ'M
  refine ⟨f,WeightedCoeff.reflection ((s+1:ℕ):ℝ) g,hf,?_,hfn,?_⟩
  · intro n
    rw [WeightedCoeff.reflection_apply,hg (-n),Int.natAbs_neg]
    split_ifs with hn
    · have hz : (Real.pi:ℂ)*(-n)+δ' (-n) = -((Real.pi:ℂ)*n+δ n) := by
        change (Real.pi:ℂ)*(-n)-δ (-(-n)) = -((Real.pi:ℂ)*n+δ n)
        simp only [neg_neg]
        ring
      have he : I*((Real.pi:ℂ)*(-n)) = -I*((Real.pi:ℂ)*n) := by ring
      simp only [Int.cast_neg]
      rw [hz,he]
      simp only [cd,WeightedCoeff.neg_val]
      ring
    · rfl
  · simpa only [LinearIsometryEquiv.norm_map] using hgn

end NLS.ZakharovShabat
