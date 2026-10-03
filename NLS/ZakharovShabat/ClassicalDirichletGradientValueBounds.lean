import NLS.ZakharovShabat.ClassicalDirichletNormalizationBounds

/-! # Pointwise bounds for the normalized Dirichlet gradient error

The squared eigenfunction error and the inverse normalization error control
the actual normalized gradient minus its exact free counterpart.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Squaring both components preserves the common Lipschitz product bound. -/
theorem norm_component_squares_sub_le (u v : ℂ × ℂ) (E D : ℝ)
    (hu : ‖u‖ ≤ E) (hv : ‖v‖ ≤ E) (hd : ‖u-v‖ ≤ D) :
    ‖(u.2^2,u.1^2)-(v.2^2,v.1^2)‖ ≤ 2*E*D := by
  have hfst := norm_component_product_sub_le (u.1,u.1) (v.1,v.1) E D
    (by simpa using (norm_fst_le u).trans hu) (by simpa using (norm_fst_le v).trans hv)
    (by simpa using (norm_fst_le (u-v)).trans hd)
  have hsnd := norm_component_product_sub_le (u.2,u.2) (v.2,v.2) E D
    (by simpa using (norm_snd_le u).trans hu) (by simpa using (norm_snd_le v).trans hv)
    (by simpa using (norm_snd_le (u-v)).trans hd)
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,← pow_two,max_le_iff] using And.intro hsnd hfst

/-- An inverse normalization bound and a solution error yield the actual
normalized gradient error against the free wave pair. -/
theorem norm_classicalDirichletNormalizedGradient_sub_free_of_bounds
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (t : Icc (0 : ℝ) 1) (E D R : ℝ)
    (hu : ‖classicalDirichletEigenfunction Φ z t‖ ≤ E)
    (hv : ‖classicalDirichletEigenfunction 0 w t‖ ≤ E)
    (hv1 : ‖classicalDirichletEigenfunction 0 w t‖ ≤ 1)
    (hd : ‖classicalDirichletEigenfunction Φ z t-classicalDirichletEigenfunction 0 w t‖ ≤ D)
    (hQ1 : ‖classicalDirichletNormalization Φ z-2‖ ≤ 1)
    (hQR : ‖classicalDirichletNormalization Φ z-2‖ ≤ R) :
    ‖classicalDirichletNormalizedGradient Φ z t-classicalDirichletNormalizedGradient 0 w t‖ ≤
      2*E*D+R/2 := by
  let Q := classicalDirichletNormalization Φ z
  let u := classicalDirichletEigenfunction Φ z t
  let v := classicalDirichletEigenfunction 0 w t
  let A : ℂ × ℂ := (u.2^2,u.1^2)
  let B : ℂ × ℂ := (v.2^2,v.1^2)
  have hA : ‖A-B‖ ≤ 2*E*D := norm_component_squares_sub_le u v E D hu hv hd
  have hB : ‖B‖ ≤ 1 := by
    have h₁ : ‖v.1‖ ≤ 1 := (norm_fst_le v).trans hv1
    have h₂ : ‖v.2‖ ≤ 1 := (norm_snd_le v).trans hv1
    change max ‖v.2^2‖ ‖v.1^2‖ ≤ 1
    rw [norm_pow,norm_pow,max_le_iff]
    constructor <;> nlinarith [norm_nonneg v.1,norm_nonneg v.2]
  obtain ⟨_,hinv,herr⟩ := classicalDirichletNormalization_inverse_bounds Φ z hQ1
  have hR : 0 ≤ R := (norm_nonneg _).trans hQR
  have hi : ‖Q⁻¹-(2 : ℂ)⁻¹‖ ≤ R/2 := herr.trans (div_le_div_of_nonneg_right hQR (by norm_num))
  have he : classicalDirichletNormalizedGradient Φ z t-classicalDirichletNormalizedGradient 0 w t =
      Q⁻¹ • (A-B)+(Q⁻¹-(2 : ℂ)⁻¹) • B := by
    apply Prod.ext <;> simp only [classicalDirichletNormalizedGradient,classicalDirichletNormalization_free,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,A,B,u,v,Q,
      div_eq_mul_inv] <;> ring
  rw [he]
  calc
    _ ≤ ‖Q⁻¹‖*‖A-B‖+‖Q⁻¹-(2 : ℂ)⁻¹‖*‖B‖ := by simpa only [norm_smul] using norm_add_le (Q⁻¹ • (A-B)) ((Q⁻¹-(2 : ℂ)⁻¹) • B)
    _ ≤ 1*(2*E*D)+(R/2)*1 := add_le_add
      (mul_le_mul hinv hA (norm_nonneg _) (by norm_num))
      (mul_le_mul hi hB (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- Under inverse-index root displacement and normalization error, the
actual normalized gradient differs from the exact free waves by O(1/|n|). -/
theorem norm_classicalDirichletNormalizedGradient_sub_free_sobolev_le
    (M B C : ℝ) (hB : 0 ≤ B) (a : Domain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (hBn : B ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (hQ1 : ‖classicalDirichletNormalization (classicalSobolevPotential a) z-2‖ ≤ 1)
    (hQ : ‖classicalDirichletNormalization (classicalSobolevPotential a) z-2‖ ≤ C/(n.natAbs : ℝ))
    (t : Icc (0 : ℝ) 1) :
    ‖classicalDirichletNormalizedGradient (classicalSobolevPotential a) z t-
        classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) t‖ ≤
      (2*Real.exp (4*M+B)*(classicalSobolevErrorConstant M B+2*B)+C/2)/(n.natAbs : ℝ) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M := (norm_classicalSobolevPotential_le a).trans (by linarith)
  have him : |z.im| ≤ B := by
    simpa using (Complex.abs_im_le_norm (z-(Real.pi : ℂ)*n)).trans (hδ.trans (div_le_self hB hn))
  have hw : |(((Real.pi : ℂ)*n)).im| ≤ B := by simpa using hB
  have hpoint := norm_classicalDirichletNormalizedGradient_sub_free_of_bounds
    (classicalSobolevPotential a) z ((Real.pi : ℂ)*n) t (Real.exp (4*M+B))
    ((classicalSobolevErrorConstant M B+2*B)/(n.natAbs : ℝ)) (C/(n.natAbs : ℝ))
    (norm_classicalSolution_unit_strip_le (4*M) B _ hφ z him (1,1) (by simp) t)
    (norm_classicalSolution_unit_strip_le (4*M) B 0 (by simpa using (show 0 ≤ 4*M by positivity))
      _ hw (1,1) (by simp) t) ?_ ?_ hQ1 hQ
  · exact hpoint.trans_eq (by ring)
  · have h := norm_classicalSolution_unit_strip_le 0 0 0 (by simp) ((Real.pi : ℂ)*n)
      (by simp) (1,1) (by simp) t
    simpa [classicalDirichletEigenfunction] using h
  · have hδ' : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ) := by simpa using hδ
    have h := (classicalShiftedFreeRemainder_time_bounds M B hB a ha n hn hBn z hδ' (1,1) t).1
    change ‖classicalSolution (classicalSobolevPotential a) z (1,1) t-classicalSolution 0 _ (1,1) t‖ ≤ _
    rw [classicalSolution_free]
    simpa [classicalShiftedFreeRemainder,classicalFreeVector] using h

end NLS.ZakharovShabat
