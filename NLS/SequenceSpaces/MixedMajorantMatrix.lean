import NLS.SequenceSpaces.ConvolutionMatrixAnalytic
import NLS.SequenceSpaces.RankOneDominatedMatrix

/-! # Analytic matrices with convolution and outer-product majorants

A single bounded matrix symbol assembles both bounded operators. Dividing
actual analytic entries by the strictly positive combined majorant then
gives operator-norm analyticity, including the non-convolution tail.
-/
noncomputable section
open Set Metric
namespace NLS.Coeff

def mixedMatrixMajorant (b : Coeff 1) (u v : Coeff 2) (m n : ℤ) : ℝ :=
  ‖b (m-n)‖+‖u m‖*‖v n‖

theorem mixedMatrixMajorant_pos (b : Coeff 1) (hb : ∀ d, b d ≠ 0)
    (u v : Coeff 2) (m n : ℤ) : 0 < mixedMatrixMajorant b u v m n :=
  add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (hb _)) (by positivity)

theorem exists_mixed_matrix_assembly (b : Coeff 1) (u v : Coeff 2) (e : ℤ ≃ ℤ × ℤ) :
    ∃ L : Coeff ⊤ →L[ℂ] (Coeff 2 →L[ℂ] Coeff 2), ‖L‖ ≤ ‖b‖+‖u‖*‖v‖ ∧
      ∀ s : Coeff ⊤, ∀ m n : ℤ,
        (L s (lp.single 2 n 1)) m = (mixedMatrixMajorant b u v m n : ℂ)*s (e.symm (m,n)) := by
  have hex (s : Coeff ⊤) : ∃ T : Coeff 2 →L[ℂ] Coeff 2,
      ‖T‖ ≤ (‖b‖+‖u‖*‖v‖)*‖s‖ ∧ ∀ m n : ℤ,
        (T (lp.single 2 n 1)) m = (mixedMatrixMajorant b u v m n : ℂ)*s (e.symm (m,n)) := by
    let B (m n : ℤ) : ℂ := (‖b (m-n)‖ : ℂ)*s (e.symm (m,n))
    let H (m n : ℤ) : ℂ := (‖u m‖ : ℂ)*(‖v n‖ : ℂ)*s (e.symm (m,n))
    have hs (m n : ℤ) : ‖s (e.symm (m,n))‖ ≤ ‖s‖ :=
      lp.norm_apply_le_norm (by simp : (⊤ : ENNReal) ≠ 0) s _
    have hB (m n : ℤ) : ‖B m n‖ ≤ ‖((‖s‖ : ℂ) • b) (m-n)‖ := by
      change ‖(‖b (m-n)‖ : ℂ)*s (e.symm (m,n))‖ ≤ ‖(‖s‖ : ℂ)*b (m-n)‖
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      nlinarith [hs m n,norm_nonneg (b (m-n))]
    obtain ⟨TB,hTB,hBentry⟩ := exists_operator_of_convolution_dominated_matrix (p := 2) B ((‖s‖ : ℂ) • b) hB
    have hH (m n : ℤ) : ‖H m n‖ ≤ ‖((‖s‖ : ℂ) • u) m‖*‖v n‖ := by
      change ‖(‖u m‖ : ℂ)*(‖v n‖ : ℂ)*s (e.symm (m,n))‖ ≤ ‖(‖s‖ : ℂ)*u m‖*‖v n‖
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      nlinarith [mul_le_mul_of_nonneg_left (hs m n) (mul_nonneg (norm_nonneg (u m)) (norm_nonneg (v n)))]
    obtain ⟨TH,hTH,hHentry⟩ := exists_operator_of_outer_product_dominated_matrix H ((‖s‖ : ℂ) • u) v hH
    refine ⟨TB+TH,?_,?_⟩
    · have hnorm := (norm_add_le TB TH).trans (add_le_add hTB hTH)
      simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg s),
        add_mul,mul_assoc,mul_left_comm,mul_comm] using hnorm
    intro m n
    simp only [add_apply,lp.coeFn_add,Pi.add_apply,hBentry,hHentry,B,H,mixedMatrixMajorant,
      Complex.ofReal_add,Complex.ofReal_mul,add_mul]
  choose Q hQnorm hQentry using hex
  let L0 : Coeff ⊤ →ₗ[ℂ] (Coeff 2 →L[ℂ] Coeff 2) := {
    toFun := Q
    map_add' := by
      intro s t
      apply continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
      intro n
      ext m
      simp only [hQentry,add_apply,lp.coeFn_add,Pi.add_apply,mul_add]
    map_smul' := by
      intro c s
      apply continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
      intro n
      ext m
      simp only [hQentry,smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      ring }
  let L : Coeff ⊤ →L[ℂ] (Coeff 2 →L[ℂ] Coeff 2) :=
    L0.mkContinuous (‖b‖+‖u‖*‖v‖) hQnorm
  exact ⟨L,ContinuousLinearMap.opNorm_le_bound _ (by positivity) hQnorm,hQentry⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_analytic_operator_of_mixed_majorant_matrix
    (F : E → ℤ → ℤ → ℂ) (V : Set E) (hV : IsOpen V)
    (hcoord : ∀ m n, AnalyticOnNhd ℂ (fun x => F x m n) V)
    (b : Coeff 1) (hb : ∀ d, b d ≠ 0) (u v : Coeff 2) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ V, ∀ m n, ‖F x m n‖ ≤ M*mixedMatrixMajorant b u v m n) :
    ∃ T : E → (Coeff 2 →L[ℂ] Coeff 2), AnalyticOnNhd ℂ T V ∧
      (∀ x ∈ V, ‖T x‖ ≤ M*(‖b‖+‖u‖*‖v‖)) ∧
      ∀ x ∈ V, ∀ m n : ℤ, (T x (lp.single 2 n 1)) m = F x m n := by
  classical
  let e : ℤ ≃ ℤ × ℤ := (Denumerable.eqv ℤ).trans (Denumerable.eqv (ℤ × ℤ)).symm
  let f (x : E) (i : ℤ) : ℂ := F x (e i).1 (e i).2/(mixedMatrixMajorant b u v (e i).1 (e i).2 : ℂ)
  have hfbound (x : E) (hx : x ∈ V) (i : ℤ) : ‖f x i‖ ≤ M := by
    dsimp only [f]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mixedMatrixMajorant_pos b hb u v _ _)]
    exact (div_le_iff₀ (mixedMatrixMajorant_pos b hb u v _ _)).mpr (hbound x hx _ _)
  let S (x : E) : Coeff ⊤ := if hx : x ∈ V then
    ⟨f x,memℓp_infty ⟨M,by rintro _ ⟨i,rfl⟩;exact hfbound x hx i⟩⟩ else 0
  have hS (x : E) (hx : x ∈ V) (i : ℤ) : S x i = f x i := by simp only [S,dif_pos hx]
  have hSnorm (x : E) (hx : x ∈ V) : ‖S x‖ ≤ M := by
    apply lp.norm_le_of_forall_le hM
    intro i
    rw [hS x hx i]
    exact hfbound x hx i
  have hScoord (i : ℤ) : AnalyticOnNhd ℂ (fun x => S x i) V := by
    intro x hx
    have he : (fun y => f y i) =ᶠ[nhds x] (fun y => S y i) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact (hS y hy i).symm
    exact ((hcoord _ _ x hx).div_const).congr he
  have haS := analyticOnNhd_of_bounded_coordinatewise S hV hScoord M hSnorm
  obtain ⟨L,hL,hentry⟩ := exists_mixed_matrix_assembly b u v e
  refine ⟨fun x => L (S x),fun x hx => (L.analyticAt _).comp (haS x hx),?_,?_⟩
  · intro x hx
    exact (L.le_opNorm (S x)).trans
      (by simpa only [mul_comm] using mul_le_mul hL (hSnorm x hx) (norm_nonneg _) (by positivity))
  intro x hx m n
  rw [hentry,hS x hx]
  simp only [f,Equiv.apply_symm_apply]
  have hc : (mixedMatrixMajorant b u v m n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (mixedMatrixMajorant_pos b hb u v m n))
  field_simp

end NLS.Coeff
