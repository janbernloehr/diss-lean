import NLS.ZakharovShabat.ClassicalDirichletGradientNormalization
import NLS.ZakharovShabat.ClassicalEndpointGradientBounds
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds

/-! # Uniform bounds for the bilinear Dirichlet normalization

The actual solution error controls the product of the two eigenfunction
components. Integration gives Q-2=O(1/|z|) on physical H¹ balls and strips,
so the normalization is uniformly separated from zero at high frequency.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- A common vector bound and vector difference bound control the bilinear
product without imposing a reality or conjugacy condition. -/
theorem norm_component_product_sub_le (u v : ℂ × ℂ) (E D : ℝ)
    (hu : ‖u‖ ≤ E) (hv : ‖v‖ ≤ E) (hd : ‖u-v‖ ≤ D) :
    ‖u.1*u.2-v.1*v.2‖ ≤ 2*E*D := by
  have hE : 0 ≤ E := (norm_nonneg u).trans hu
  have hD : 0 ≤ D := (norm_nonneg (u-v)).trans hd
  have h₁ : ‖u.1-v.1‖ ≤ D := (norm_fst_le (u-v)).trans hd
  have h₂ : ‖u.2-v.2‖ ≤ D := (norm_snd_le (u-v)).trans hd
  calc
    _ = ‖(u.1-v.1)*u.2+v.1*(u.2-v.2)‖ := by congr 1; ring
    _ ≤ ‖u.1-v.1‖*‖u.2‖+‖v.1‖*‖u.2-v.2‖ := by
      simpa only [norm_mul] using norm_add_le ((u.1-v.1)*u.2) (v.1*(u.2-v.2))
    _ ≤ D*E+E*D := add_le_add
      (mul_le_mul h₁ ((norm_snd_le u).trans hu) (norm_nonneg _) hD)
      (mul_le_mul ((norm_fst_le v).trans hv) h₂ (norm_nonneg _) hE)
    _ = _ := by ring

/-- The normalization error is bounded by four times the solution-size
bound times its free-solution error, with any free spectral parameter. -/
theorem norm_classicalDirichletNormalization_sub_two_of_bounds
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (E D : ℝ)
    (h : ∀ t : Icc (0 : ℝ) 1,
      ‖classicalDirichletEigenfunction Φ z t‖ ≤ E ∧
      ‖classicalDirichletEigenfunction 0 w t‖ ≤ E ∧
      ‖classicalDirichletEigenfunction Φ z t-classicalDirichletEigenfunction 0 w t‖ ≤ D) :
    ‖classicalDirichletNormalization Φ z-2‖ ≤ 4*E*D := by
  let f : ℝ → ℂ := fun t => (classicalDirichletEigenfunction Φ z t).1*(classicalDirichletEigenfunction Φ z t).2
  let g : ℝ → ℂ := fun t => (classicalDirichletEigenfunction 0 w t).1*(classicalDirichletEigenfunction 0 w t).2
  have hf : Continuous f := by
    exact (continuous_classicalSolution Φ z (1,1)).fst.mul (continuous_classicalSolution Φ z (1,1)).snd
  have hg : Continuous g := by
    exact (continuous_classicalSolution 0 w (1,1)).fst.mul (continuous_classicalSolution 0 w (1,1)).snd
  have he : classicalDirichletNormalization Φ z-2 = 2*∫ t in (0 : ℝ)..1, f t-g t := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    change 2*(∫ t in (0 : ℝ)..1, f t)-2 = _
    have hfree : 2*(∫ t in (0 : ℝ)..1, g t) = 2 := classicalDirichletNormalization_free w
    linear_combination hfree
  have hb : ‖∫ t in (0 : ℝ)..1, f t-g t‖ ≤ 2*E*D := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := 2*E*D) (f := fun t => f t-g t) (by
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          have : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
          exact Ioc_subset_Icc_self this
        exact norm_component_product_sub_le _ _ E D (h ⟨t,ht'⟩).1 (h ⟨t,ht'⟩).2.1 (h ⟨t,ht'⟩).2.2)
    simpa using hi
  rw [he,norm_mul]
  norm_num only [norm_ofNat]
  nlinarith

/-- Uniform numerator for the actual normalization error on a Sobolev ball and strip. -/
def classicalDirichletNormalizationErrorConstant (M H : ℝ) : ℝ :=
  4*Real.exp (4*M+H)*classicalSobolevErrorConstant M H

theorem classicalDirichletNormalizationErrorConstant_nonneg (M H : ℝ) (hM : 0 ≤ M) :
    0 ≤ classicalDirichletNormalizationErrorConstant M H := by
  unfold classicalDirichletNormalizationErrorConstant
  exact mul_nonneg (by positivity) (classicalSobolevErrorConstant_nonneg M H hM)

/-- The bilinear normalization converges uniformly to two at inverse spectral frequency. -/
theorem norm_classicalDirichletNormalization_sub_two_sobolev_strip_le
    (M H : ℝ) (a : Domain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (him : |z.im| ≤ H) :
    ‖classicalDirichletNormalization (classicalSobolevPotential a) z-2‖ ≤
      classicalDirichletNormalizationErrorConstant M H/‖z‖ := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M :=
    (norm_classicalSobolevPotential_le a).trans (by linarith)
  have hb := norm_classicalDirichletNormalization_sub_two_of_bounds
    (classicalSobolevPotential a) z z (Real.exp (4*M+H)) (classicalSobolevErrorConstant M H/‖z‖) (by
      intro t
      refine ⟨norm_classicalSolution_unit_strip_le (4*M) H _ hφ z him (1,1) (by simp) t,
        norm_classicalSolution_unit_strip_le (4*M) H 0 (by simpa using (show 0 ≤ 4*M by positivity))
          z him (1,1) (by simp) t,?_⟩
      have hR := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz him (1,1) t
      have hv : ‖((1 : ℂ),(1 : ℂ))‖ = 1 := by simp
      rw [hv] at hR
      change ‖classicalSolution (classicalSobolevPotential a) z (1,1) t-classicalSolution 0 z (1,1) t‖ ≤ _
      rw [classicalSolution_free z (1,1) t]
      change ‖classicalSolutionRemainder (classicalSobolevPotential a) z (1,1) t‖ ≤ _
      have he : (4+Real.pi)*M*1/‖z‖*Real.exp (4*M+H) = classicalSobolevErrorConstant M H/‖z‖ := by
        unfold classicalSobolevErrorConstant
        ring
      exact hR.trans_eq he)
  exact hb.trans_eq (by unfold classicalDirichletNormalizationErrorConstant; ring)

/-- Nearness to the free normalization controls both its inverse and its
inverse error, without an independent nonzero-normalization premise. -/
theorem classicalDirichletNormalization_inverse_bounds (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hQ : ‖classicalDirichletNormalization Φ z-2‖ ≤ 1) :
    1 ≤ ‖classicalDirichletNormalization Φ z‖ ∧
    ‖(classicalDirichletNormalization Φ z)⁻¹‖ ≤ 1 ∧
    ‖(classicalDirichletNormalization Φ z)⁻¹-(2 : ℂ)⁻¹‖ ≤
      ‖classicalDirichletNormalization Φ z-2‖/2 := by
  let Q := classicalDirichletNormalization Φ z
  have hn : 1 ≤ ‖Q‖ := by
    have ht := norm_le_norm_sub_add (2 : ℂ) Q
    rw [norm_sub_rev] at ht
    norm_num at ht
    change ‖Q-2‖ ≤ 1 at hQ
    linarith
  have hne : Q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hn)
  refine ⟨hn,?_,?_⟩
  · rw [norm_inv]
    exact inv_le_one_of_one_le₀ hn
  · change ‖Q⁻¹-(2 : ℂ)⁻¹‖ ≤ ‖Q-2‖/2
    have he : Q⁻¹-(2 : ℂ)⁻¹ = -(Q-2)/(2*Q) := by field_simp; ring
    rw [he,norm_div,norm_neg,norm_mul]
    norm_num only [norm_ofNat]
    calc
      _ ≤ ‖Q-2‖/(2*1) := div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
      _ = _ := by ring

/-- Bounded displacement from the free lattice gives one cutoff for
inverse-index normalization error, a lower bound of one, and inverse error. -/
theorem exists_classicalDirichletNormalization_near_free_bounds
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Domain 2), ‖a‖ ≤ M → ∀ n : ℤ, N ≤ n.natAbs →
      ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ B →
        ‖classicalDirichletNormalization (classicalSobolevPotential a) z-2‖ ≤ C/(n.natAbs : ℝ) ∧
        1 ≤ ‖classicalDirichletNormalization (classicalSobolevPotential a) z‖ ∧
        ‖(classicalDirichletNormalization (classicalSobolevPotential a) z)⁻¹‖ ≤ 1 ∧
        ‖(classicalDirichletNormalization (classicalSobolevPotential a) z)⁻¹-(2 : ℂ)⁻¹‖ ≤
          C/(2*(n.natAbs : ℝ)) := by
  let E := classicalDirichletNormalizationErrorConstant M B
  have hE : 0 ≤ E := classicalDirichletNormalizationErrorConstant_nonneg M B hM
  let C := 2*E/Real.pi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  obtain ⟨K,hK⟩ := exists_nat_ge C
  refine ⟨max N K,hN.trans_le (le_max_left _ _),C,hC,?_⟩
  intro a ha n hn z hz
  have hnN := (le_max_left N K).trans hn
  have hnpos : 0 < (n.natAbs : ℝ) := by exact_mod_cast hN.trans_le hnN
  have hCn : C ≤ (n.natAbs : ℝ) := hK.trans (by exact_mod_cast (le_max_right N K).trans hn)
  obtain ⟨him,hz1,hzn⟩ := hcut n hnN z hz
  have hzne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1)
  have hQ : ‖classicalDirichletNormalization (classicalSobolevPotential a) z-2‖ ≤ C/(n.natAbs : ℝ) := by
    apply (norm_classicalDirichletNormalization_sub_two_sobolev_strip_le M B a ha z hzne him).trans
    calc
      E/‖z‖ ≤ E/(Real.pi*(n.natAbs : ℝ)/2) := div_le_div_of_nonneg_left hE (by positivity) hzn
      _ = C/(n.natAbs : ℝ) := by dsimp [C]; ring
  have hQ1 := hQ.trans ((div_le_one hnpos).mpr hCn)
  obtain ⟨hlo,hinv,herr⟩ := classicalDirichletNormalization_inverse_bounds (classicalSobolevPotential a) z hQ1
  refine ⟨hQ,hlo,hinv,?_⟩
  apply herr.trans
  calc
    _ ≤ (C/(n.natAbs : ℝ))/2 := div_le_div_of_nonneg_right hQ (by norm_num)
    _ = C/(2*(n.natAbs : ℝ)) := by ring

end NLS.ZakharovShabat
