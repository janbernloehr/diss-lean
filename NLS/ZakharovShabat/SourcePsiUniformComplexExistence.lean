import NLS.ZakharovShabat.SourcePsiUniformComplexBranchRealAgreement

/-!
# An index-independent local complex extension of the canonical psi roots

At every real source, all deleted indices admit analytic root branches
on one source ball. On its real locus they are the canonical gap roots;
throughout the complex ball they satisfy the actual retained contour
orthogonality equations and stay in a common ball about the base roots.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_uniform_local_sourcePsi_complexRoot_branches
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        (∀ n, AnalyticOnNhd ℂ (s n) (ball φ.val δ)) ∧
        (∀ n, ∀ χ : realTypeSourceLocus p, χ.val ∈ ball φ.val δ →
          s n χ.val = sourcePsiGapRoot hp hp1 n χ) ∧
        ∀ n, ∀ ψ ∈ ball φ.val δ,
          ‖s n ψ-sourcePsiGapRoot hp hp1 n φ‖ < ρ ∧
          ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
            sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
            ∀ m : ℤ, m ≠ n →
              sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) (R m) = 0 := by
  obtain ⟨D⟩ := nonempty_sourcePsiUniformEquationTube hp hp1 φ
  obtain ⟨S⟩ := nonempty_sourcePsiUniformComplexBranchFamily D
  refine ⟨S.sourceRadius,S.rootRadius,S.sourceRadius_pos,S.rootRadius_pos,
    S.branch,S.analytic,(fun n χ hχ => S.eq_sourcePsiGapRoot_of_real n χ hχ),?_⟩
  intro n ψ hψ
  have hdist : max (dist (S.branch n ψ) (sourcePsiGapRoot hp hp1 n φ)) (dist ψ φ.val) < S.rootRadius := by
    simpa only [mem_ball,Prod.dist_eq] using S.graph n ψ hψ
  refine ⟨by simpa only [dist_eq_norm] using (le_max_left _ _).trans_lt hdist,?_⟩
  obtain ⟨c,R,hfamily,hcoord⟩ := S.contour_equations n ψ hψ
  refine ⟨c,R,hfamily,?_⟩
  intro m hmn
  have hnm : ((n-m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  have hπ : (2*Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hzero := hcoord m
  rw [sourcePsiEquationCoordinate] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hnm hπ)

end NLS.ZakharovShabat
