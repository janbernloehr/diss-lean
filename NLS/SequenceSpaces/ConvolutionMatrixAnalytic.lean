import NLS.SequenceSpaces.ConvolutionDominatedMatrix
import NLS.SequenceSpaces.OperatorBasisExt
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Operator-norm analyticity of convolution-dominated matrices

Divide entries by a nonvanishing summable majorant. The bounded matrix
symbol is an analytic l-infinity map; a bounded linear assembly map gives
analyticity in the actual operator norm, rather than only entrywise.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.Coeff

theorem exists_convolution_matrix_assembly (b : Coeff 1) (e : ℤ ≃ ℤ × ℤ) :
    ∃ L : Coeff ⊤ →L[ℂ] (Coeff 2 →L[ℂ] Coeff 2), ‖L‖ ≤ ‖b‖ ∧
      ∀ s : Coeff ⊤, ∀ m n : ℤ,
        (L s (lp.single 2 n 1)) m = b (m-n)*s (e.symm (m,n)) := by
  have hex (s : Coeff ⊤) : ∃ T : Coeff 2 →L[ℂ] Coeff 2,
      ‖T‖ ≤ ‖b‖*‖s‖ ∧ ∀ m n : ℤ,
        (T (lp.single 2 n 1)) m = b (m-n)*s (e.symm (m,n)) := by
    let c : Coeff 1 := (‖s‖ : ℂ) • b
    have hdom (m n : ℤ) : ‖b (m-n)*s (e.symm (m,n))‖ ≤ ‖c (m-n)‖ := by
      change _ ≤ ‖(‖s‖ : ℂ)*b (m-n)‖
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg s)]
      nlinarith [lp.norm_apply_le_norm (by simp : (⊤ : ENNReal) ≠ 0) s (e.symm (m,n)),
        norm_nonneg (b (m-n))]
    obtain ⟨T,hT,hentry⟩ := exists_operator_of_convolution_dominated_matrix
      (p := 2) (fun m n => b (m-n)*s (e.symm (m,n))) c hdom
    refine ⟨T,hT.trans_eq ?_,hentry⟩
    simp only [c,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg s),mul_comm]
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
  let L : Coeff ⊤ →L[ℂ] (Coeff 2 →L[ℂ] Coeff 2) := L0.mkContinuous ‖b‖ hQnorm
  refine ⟨L,?_,hQentry⟩
  exact ContinuousLinearMap.opNorm_le_bound L (norm_nonneg b) hQnorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Local bounded convolution domination and analytic scalar entries
construct an operator-norm analytic family with the exact matrix. -/
theorem exists_analytic_operator_of_convolution_dominated_matrix
    (F : E → ℤ → ℤ → ℂ) (V : Set E) (hV : IsOpen V)
    (hcoord : ∀ m n, AnalyticOnNhd ℂ (fun x => F x m n) V)
    (b : Coeff 1) (hb : ∀ d : ℤ, b d ≠ 0) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ V, ∀ m n, ‖F x m n‖ ≤ M*‖b (m-n)‖) :
    ∃ T : E → (Coeff 2 →L[ℂ] Coeff 2), AnalyticOnNhd ℂ T V ∧
      (∀ x ∈ V, ‖T x‖ ≤ M*‖b‖) ∧
      ∀ x ∈ V, ∀ m n : ℤ, (T x (lp.single 2 n 1)) m = F x m n := by
  classical
  let e : ℤ ≃ ℤ × ℤ := (Denumerable.eqv ℤ).trans (Denumerable.eqv (ℤ × ℤ)).symm
  let f (x : E) (i : ℤ) : ℂ := F x (e i).1 (e i).2/b ((e i).1-(e i).2)
  have hfbound (x : E) (hx : x ∈ V) (i : ℤ) : ‖f x i‖ ≤ M := by
    rw [show f x i = F x (e i).1 (e i).2/b ((e i).1-(e i).2) from rfl,norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (hb _))).mpr (hbound x hx _ _)
  let S (x : E) : Coeff ⊤ := if hx : x ∈ V then
    ⟨f x,memℓp_infty ⟨M,by rintro _ ⟨i,rfl⟩; exact hfbound x hx i⟩⟩ else 0
  have hS (x : E) (hx : x ∈ V) (i : ℤ) : S x i = f x i := by
    simp only [S,dif_pos hx]
  have hSbound (x : E) (hx : x ∈ V) : ‖S x‖ ≤ M := by
    apply lp.norm_le_of_forall_le hM
    intro i
    rw [hS x hx i]
    exact hfbound x hx i
  have hScoord (i : ℤ) : AnalyticOnNhd ℂ (fun x => S x i) V := by
    intro x hx
    have he : (fun y => f y i) =ᶠ[𝓝 x] (fun y => S y i) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact (hS y hy i).symm
    exact ((hcoord (e i).1 (e i).2 x hx).div_const).congr he
  have haS := analyticOnNhd_of_bounded_coordinatewise S hV hScoord M hSbound
  obtain ⟨L,hL,hentry⟩ := exists_convolution_matrix_assembly b e
  refine ⟨fun x => L (S x),fun x hx => (L.analyticAt _).comp (haS x hx),?_,?_⟩
  · intro x hx
    have he := (L.le_opNorm (S x)).trans
      (mul_le_mul hL (hSbound x hx) (norm_nonneg _) (norm_nonneg b))
    simpa only [mul_comm] using he
  intro x hx m n
  rw [hentry,hS x hx]
  dsimp only [f]
  rw [e.apply_symm_apply]
  field_simp [hb (m-n)]

end NLS.Coeff
