import NLS.Articles.KdVPseudomeasures.SourceLemma210

/-! Lemma 2.10 on arbitrary raw test coefficients. The weighted infinity
norm is an extended supremum, so no weighted membership is added to the
paper's unweighted test-function hypothesis. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- The exact shifted weighted supremum, including infinity. -/
def sourceShiftedENorm (W : Weight) (l : ℤ) (f : ℤ → ℂ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ENNReal.ofReal (W (k+l)*‖f k‖)

theorem source_exists_weighted_of_shift_bound (w : SpectralWeight) (r : ℝ) (hr : 0≤r)
    (l : ℤ) (f : ℤ → ℂ) (M : ℝ) (hM : 0≤M)
    (hb : ∀ k, w.negativeSobolev r (k+l)*‖f k‖≤M) :
    ∃ F : WeightedCoeff (w.negativeSobolev r) ⊤,
      (∀ k, F.val k=f k) ∧ w.negativeShiftedNorm r hr l ⊤ F≤M := by
  let W := (w.negativeSobolev r).shift l
  have hpoint (k : ℤ) : ‖(W k:ℂ)*f k‖≤M := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (W.positive k),
      W,Weight.shift_apply,abs_of_pos ((w.negativeSobolev r).positive (k+l))] using hb k
  let G : WeightedCoeff W ⊤ := ⟨f,memℓp_infty ⟨M,by rintro _ ⟨k,rfl⟩; exact hpoint k⟩⟩
  let F := (w.negativeShiftEquiv r hr l ⊤).symm G
  refine ⟨F,fun k => w.negativeShiftEquiv_symm_apply r hr l ⊤ G k,?_⟩
  change ‖w.negativeShiftEquiv r hr l ⊤ ((w.negativeShiftEquiv r hr l ⊤).symm G)‖≤M
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact lp.norm_le_of_forall_le hM hpoint

/-- Both signed rows, with the source norm interpreted as the extended
supremum on its full raw domain. The same constant works for every weight. -/
theorem sourceLemma2_10_extended (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ 13*endpointHillConstant r≤C ∧
      ∀ (w : SpectralWeight) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
      (f : ℤ → ℂ) (n : ℕ) (_hn : 2≤n) (z : ℂ) (_hz : z ∈ wideHillStrip n)
      (l : ℤ), (l=(n:ℤ) ∨ l=-(n:ℤ)) →
        ENNReal.ofReal (w.negativeSobolev r (2*(n:ℤ))*
          ‖∑' k : ℤ, q.val (l-k)*wideHillSymbol n z k*f k‖) ≤
          ENNReal.ofReal (C*sourcePredualEpsilon r n*‖q‖)*
            sourceShiftedENorm (w.negativeSobolev r) l f := by
  obtain ⟨C,hC,hCwide,h⟩ := sourceLemma2_10 r hr hr1
  refine ⟨C,hC,hCwide,?_⟩
  intro w q f n hn z hz l hl
  by_cases hq : q=0
  · subst q
    simp only [zero_val,zero_mul,tsum_zero,norm_zero,mul_zero,ENNReal.ofReal_zero,
      zero_mul,le_refl]
  have hA : 0<C*sourcePredualEpsilon r n*‖q‖ := by
    have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have he : 0<sourcePredualEpsilon r n := by
      unfold sourcePredualEpsilon
      split_ifs
      · exact div_pos (Real.log_pos (by linarith)) hnp
      · positivity
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hC) he) (norm_pos_iff.mpr hq)
  by_cases hf : sourceShiftedENorm (w.negativeSobolev r) l f=⊤
  · rw [hf,ENNReal.mul_top (by simpa only [ne_eq,ENNReal.ofReal_eq_zero] using not_le_of_gt hA)]
    exact le_top
  obtain ⟨F,hF,hFn⟩ := source_exists_weighted_of_shift_bound w r hr l f
    (sourceShiftedENorm (w.negativeSobolev r) l f).toReal ENNReal.toReal_nonneg (fun k =>
      (ENNReal.ofReal_le_iff_le_toReal hf).mp (le_iSup (fun j : ℤ =>
        ENNReal.ofReal (w.negativeSobolev r (j+l)*‖f j‖)) k))
  have hb : w.negativeSobolev r (2*(n:ℤ))*
      ‖∑' k : ℤ, q.val (l-k)*wideHillSymbol n z k*f k‖ ≤
        (C*sourcePredualEpsilon r n*‖q‖)*w.negativeShiftedNorm r hr l ⊤ F := by
    have hh := h w q F n hn z hz
    rcases hl with rfl | rfl
    · simpa only [wideEndpointHillPerturbation_apply,hF] using hh.1
    · simpa only [wideEndpointHillPerturbation_apply,hF] using hh.2
  calc
    _ ≤ ENNReal.ofReal ((C*sourcePredualEpsilon r n*‖q‖)*
        (sourceShiftedENorm (w.negativeSobolev r) l f).toReal) :=
      ENNReal.ofReal_le_ofReal (hb.trans (mul_le_mul_of_nonneg_left hFn hA.le))
    _ = _ := by rw [ENNReal.ofReal_mul hA.le,ENNReal.ofReal_toReal hf]

end NLS.Articles.KdVPseudomeasures
