import NLS.ZakharovShabat.SobolevWKBInitialBasis

/-! # Uniform WKB models for both standard fundamental columns

The models retain the exact initial-basis normalization and both leading density integrals. Their order-(N+1) errors are uniform on original Hs balls for s >= 1 and N <= s.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- First normalized fundamental-column model, with both actual leading
oscillatory density terms and the exact initial-basis normalization. -/
def nlsWKBFirstColumnModel (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ × ℂ :=
  (1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z)⁻¹ •
    ((nlsWKBVector a b N z t-(0,nlsWKBLeadingTerm a b N z t))-
      nlsWKBInitialLower a b N z •
        (nlsWKBSecondVector a b N z t-(nlsWKBLeadingTerm (-b) (-a) N (-z) t,0)))

/-- Second normalized fundamental-column model using the same initial basis. -/
def nlsWKBSecondColumnModel (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ × ℂ :=
  (1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z)⁻¹ •
    ((nlsWKBSecondVector a b N z t-(nlsWKBLeadingTerm (-b) (-a) N (-z) t,0))-
      nlsWKBInitialUpper a b N z •
        (nlsWKBVector a b N z t-(0,nlsWKBLeadingTerm a b N z t)))

/-- Both standard fundamental columns admit the explicit WKB models with
uniform order-(N+1) errors on the original Hs ball and a spectral strip. -/
theorem exists_uniform_nlsWKB_fundamental_columns_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, T ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (1,0) t-
          nlsWKBFirstColumnModel a b N z t‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) ∧
        ‖classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (0,1) t-
          nlsWKBSecondColumnModel a b N z t‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨T,hT,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s N hNs R hR
  obtain ⟨C₁,hC₁,hfirst⟩ := exists_uniform_nlsWKB_leading_oscillatory_error_bound s N hs hNs R hR H
  obtain ⟨C₂,hC₂,hsecond⟩ := exists_uniform_nlsWKB_second_leading_oscillatory_error_bound s N hs hNs R hR H
  refine ⟨T,hT,4*(C₁+C₂),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  let U := classicalSolution Φ z (1,p) t
  let V := classicalSolution Φ z (q,1) t
  let A := nlsWKBVector a b N z t-(0,nlsWKBLeadingTerm a b N z t)
  let B := nlsWKBSecondVector a b N z t-(nlsWKBLeadingTerm (-b) (-a) N (-z) t,0)
  let ε := (C₁+C₂)*‖(2*I*z)⁻¹‖^(N+1)
  obtain ⟨hp,hq,hdet,_⟩ := hbasis ab hab a b ha hb hpa hpb hca hcb z hz
  have hpq : ‖p*q‖ ≤ 1/2 := by
    rw [norm_mul]
    have hm := mul_le_mul hp hq (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  have h₁ := hfirst ab hab a b ha hb hpa hpb hca hcb z (hT.trans hz) hzH t
  have h₂ := hsecond ab hab a b ha hb hpa hpb hca hcb z (hT.trans hz) hzH t
  rw [nlsWKBVector_initial] at h₁
  rw [nlsWKBSecondVector_initial] at h₂
  have hUA : ‖U-A‖ ≤ ε := by
    have he : U-A = -(nlsWKBVector a b N z t-U-(0,nlsWKBLeadingTerm a b N z t)) := by
      dsimp only [A]
      abel
    rw [he,norm_neg]
    apply h₁.trans
    exact mul_le_mul_of_nonneg_right (by linarith : C₁ ≤ C₁+C₂) (by positivity)
  have hVB : ‖V-B‖ ≤ ε := by
    have he : V-B = -(nlsWKBSecondVector a b N z t-V-(nlsWKBLeadingTerm (-b) (-a) N (-z) t,0)) := by
      dsimp only [B]
      abel
    rw [he,norm_neg]
    apply h₂.trans
    exact mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ C₁+C₂) (by positivity)
  have hrec := norm_basis_reconstruction_sub_le p q hpq
    (hp.trans (by norm_num)) (hq.trans (by norm_num)) U V A B ε hUA hVB
  change ‖(1-p*q)⁻¹ • (classicalSolution Φ z (1,p) t-p • classicalSolution Φ z (q,1) t)-
      nlsWKBFirstColumnModel a b N z t‖ ≤ 4*ε ∧
    ‖(1-p*q)⁻¹ • (classicalSolution Φ z (q,1) t-q • classicalSolution Φ z (1,p) t)-
      nlsWKBSecondColumnModel a b N z t‖ ≤ 4*ε at hrec
  rw [← classicalSolution_from_basis_left Φ z p q hdet t,
    ← classicalSolution_from_basis_right Φ z p q hdet t] at hrec
  exact ⟨hrec.1.trans_eq (by dsimp [ε]; ring),hrec.2.trans_eq (by dsimp [ε]; ring)⟩

end NLS.ZakharovShabat
