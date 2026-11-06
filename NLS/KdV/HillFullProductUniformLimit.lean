import NLS.ComplexAnalysis.HilbertProductDeletion
import NLS.KdV.HillAbelianHilbertProduct
import NLS.ComplexAnalysis.BanachTaylorBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The zero-deletion weight is the actual full positive reciprocal weight. -/
theorem hillAbelianHilbertWeight_zero : hillAbelianHilbertWeight 0=
    (((Real.pi : ℂ)^2)⁻¹ • Coeff.positivePuncturedLattice 2 (by norm_num)) := by
  apply (Coeff.deleteCoordinate_eq_self_iff _ _).mpr
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.positivePuncturedLattice_apply,
    Nat.cast_zero,lt_self_iff_false,if_false,mul_zero]

/-- Every omitted weight is the corresponding deletion of the full weight. -/
theorem hillAbelianHilbertWeight_eq_delete_full (n : ℕ) :
    hillAbelianHilbertWeight n=Coeff.deleteCoordinate (n : ℤ) (hillAbelianHilbertWeight 0) := by
  rw [hillAbelianHilbertWeight_zero]
  rfl

/-- The full product is restored by its actual missing factor. -/
theorem hillAbelianHilbertProduct_full_factor (n : ℕ) (t : ℂ × Coeff 2) :
    hillAbelianHilbertProduct 0 t=
      (1+hillAbelianHilbertInput t (n : ℤ)*hillAbelianHilbertWeight 0 (n : ℤ))*
        hillAbelianHilbertProduct n t := by
  change hilbertWeightedProduct (hillAbelianHilbertWeight 0) (hillAbelianHilbertInput t)=_
  rw [hilbertWeightedProduct_eq_factor_mul_deleted]
  rw [←hillAbelianHilbertWeight_eq_delete_full]
  rfl

/-- The actual omitted entire numerators converge to the full product,
uniformly on every bounded joint energy/root ball, at rate O(1/n). -/
theorem exists_hillAbelianHilbertProduct_full_uniform_bound (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 1≤n → ∀ t : ℂ × Coeff 2, ‖t‖≤B →
      ‖hillAbelianHilbertProduct n t-hillAbelianHilbertProduct 0 t‖≤C/(n : ℝ) := by
  let A := 3*B
  let D := ‖hillAbelianHilbertWeight 0‖
  let C := A*((Real.pi^2)⁻¹)*Real.exp (A*D)+1
  have hA : 0≤A := by dsimp only [A];positivity
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro n hn t ht
  have hnpos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hinput : ‖hillAbelianHilbertInput t‖≤A := by
    have hE : ‖t.1‖≤B := norm_fst_le t |>.trans ht
    have ha : ‖t.2‖≤B := norm_snd_le t |>.trans ht
    change ‖t.2-t.1 • Coeff.positivePuncturedLattice 2 (by norm_num)‖≤A
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    have hh := mul_le_mul hE Coeff.norm_positivePuncturedLattice_two_le (norm_nonneg _) hB
    dsimp only [A]
    linarith
  have hweight : ‖hillAbelianHilbertWeight 0 (n : ℤ)‖=(Real.pi^2)⁻¹/(n : ℝ) := by
    rw [hillAbelianHilbertWeight_zero]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.positivePuncturedLattice_apply,
      if_pos (show (0:ℤ)<(n : ℤ) by omega),norm_mul,norm_inv,norm_pow,norm_real,
      Real.norm_eq_abs,abs_of_nonneg Real.pi_pos.le,Int.cast_natCast,norm_natCast,div_eq_mul_inv]
  have hh := norm_hilbertWeightedProduct_deleted_sub_le (hillAbelianHilbertWeight 0)
    (hillAbelianHilbertInput t) (n : ℤ)
  rw [←hillAbelianHilbertWeight_eq_delete_full,hweight] at hh
  apply hh.trans
  have he : Real.exp (‖hillAbelianHilbertInput t‖*D)≤Real.exp (A*D) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hinput (norm_nonneg _))
  have hb := mul_le_mul (mul_le_mul_of_nonneg_right hinput (by positivity : 0≤(Real.pi^2)⁻¹/(n : ℝ))) he
    (Real.exp_pos _).le (by positivity : 0≤A*((Real.pi^2)⁻¹/(n : ℝ)))
  apply hb.trans
  change A*((Real.pi^2)⁻¹/(n : ℝ))*Real.exp (A*D)≤C/(n : ℝ)
  rw [show A*((Real.pi^2)⁻¹/(n : ℝ))*Real.exp (A*D)=
      (A*((Real.pi^2)⁻¹)*Real.exp (A*D))/(n : ℝ) by ring]
  exact div_le_div_of_nonneg_right (by dsimp only [C];linarith) hnpos.le

/-- The full joint Fréchet derivatives converge in operator norm on
bounded energy/root balls, with a common O(1/n) bound. -/
theorem exists_hillAbelianHilbertProduct_full_derivative_uniform_bound (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 1≤n → ∀ t : ℂ × Coeff 2, ‖t‖≤B →
      ‖fderiv ℂ (hillAbelianHilbertProduct n) t-fderiv ℂ (hillAbelianHilbertProduct 0) t‖≤C/(n : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillAbelianHilbertProduct_full_uniform_bound (B+2) (by positivity)
  refine ⟨2*C,by positivity,?_⟩
  intro n hn t ht
  let f : ℂ × Coeff 2 → ℂ := fun u => hillAbelianHilbertProduct n u-hillAbelianHilbertProduct 0 u
  have hf : AnalyticOnNhd ℂ f univ := (analyticOnNhd_hillAbelianHilbertProduct n).sub
    (analyticOnNhd_hillAbelianHilbertProduct 0)
  have hh := norm_fderiv_le_of_ball_bound f 0 t (B+1) 1 (C/(n : ℝ)) (by norm_num)
    (hf.differentiableOn.mono (subset_univ _)) (fun u hu => hbound n hn u (by
      have hh : ‖u‖<(B+1)+1 := by simpa only [mem_ball,dist_zero_right] using hu
      linarith)) (by simpa only [mem_ball,dist_zero_right] using (by linarith : ‖t‖<B+1))
  have hd : fderiv ℂ f t=fderiv ℂ (hillAbelianHilbertProduct n) t-fderiv ℂ (hillAbelianHilbertProduct 0) t := by
    exact (((analyticOnNhd_hillAbelianHilbertProduct n) t (mem_univ _)).differentiableAt.hasFDerivAt.sub
      (((analyticOnNhd_hillAbelianHilbertProduct 0) t (mem_univ _)).differentiableAt.hasFDerivAt)).fderiv
  rw [hd] at hh
  exact hh.trans_eq (by ring)

end NLS.KdV
