import NLS.ZakharovShabat.WKBLeadingTailFourierError
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff

/-! # Sharp Fourier tail estimate for the leading WKB integral

At full order N=s, the explicit leading integral differs from the original second coefficient by an H^(s+1) tail, uniformly on original Sobolev balls and displacement budgets.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- At the full order N=s, the actual leading WKB integral minus the
original second Fourier coefficient gains one weighted L2 derivative.
The cutoff and bound are uniform on original Hs balls and displacement budgets. -/
theorem exists_uniform_nlsWKBLeadingTerm_fourier_tail_error_bound
    (s : ℕ) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm a b s ((Real.pi:ℂ)*n+δ n) 1-
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨K,hK,hcut⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨E,hE,herror⟩ := exists_uniform_sobolevRiccati_leading_sampling_error_bound s s le_rfl R hR D M hM
  let A : ℝ := Real.exp 1*(2^s-1)+2
  have hA : 0 ≤ A := by
    have hh : (1:ℝ) ≤ 2^s := one_le_pow₀ (by norm_num)
    dsimp [A]
    positivity
  refine ⟨K,hK,A*M*R+Real.exp 1*E,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  obtain ⟨e,he,hen⟩ := herror ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  have hgeom := hcut δ (fun n => (lp.norm_apply_le_norm (by simp) δ n).trans hδD) hδM
  obtain ⟨f,hf,hfn⟩ := exists_wkb_leading_tail_fourier_error s K ab.2 e
    (fun n => (Real.pi:ℂ)*n+δ n) δ M hM (fun _ => rfl)
    (fun n hn => (hgeom n hn).1) (fun n _ => hδM n) (fun n hn => (hgeom n hn).2)
  refine ⟨f,?_,hfn.trans ?_⟩
  · intro n
    rw [hf n]
    split_ifs with hn
    · rw [he n]
      simp only [nlsWKBLeadingTerm,Complex.ofReal_one,mul_one]
      ring
    · rfl
  · exact add_le_add (mul_le_mul_of_nonneg_left ((norm_snd_le ab).trans hab) (mul_nonneg hA hM))
      (mul_le_mul_of_nonneg_left hen (Real.exp_pos 1).le)

end NLS.ZakharovShabat
