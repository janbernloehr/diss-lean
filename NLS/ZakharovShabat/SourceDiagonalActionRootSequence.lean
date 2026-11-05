import NLS.ZakharovShabat.SourceDiagonalActionRootCommonDomain

/-! # Analytic bounded symbols for the physical Cartesian scaling

The native half-order weight times the actual physical action root is a
bounded sequence analytic in its full linfinity norm. This symbol can
multiply original weighted NLS coordinates at every Sobolev level.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourceDiagonalScaledActionRoot (n : ℤ) (ψ : CoeffPair 2) : ℂ :=
  if 0 < n then (Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n ψ else 0

def sourceDiagonalActionRootSequence (ψ : CoeffPair 2) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (fun n => sourceDiagonalScaledActionRoot n ψ)

/-- All native scaling factors form one bounded Banach analytic sequence
on a common complex source neighborhood, with exact scalar coordinates. -/
theorem exists_local_sourceDiagonalActionRootSequence_analytic
    (φ : realDiagonalSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ sourceDiagonalActionRootSequence U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, sourceDiagonalActionRootSequence ψ n = sourceDiagonalScaledActionRoot n ψ := by
  obtain ⟨U,hU,hφU,hA,R,hR,hbound⟩ := exists_local_sourceDiagonalActionRoot_allIndices_analytic_bound φ
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (sourceDiagonalScaledActionRoot n) U := by
    intro ψ hψ
    change AnalyticAt ℂ (fun χ => if 0 < n then
      (Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n χ else 0) ψ
    by_cases hn : 0 < n
    · simp only [if_pos hn]
      exact analyticAt_const.mul (hA n hn ψ hψ)
    · simp only [if_neg hn]
      exact analyticAt_const
  have hb (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) : ‖sourceDiagonalScaledActionRoot n ψ‖ ≤ R := by
    by_cases hn : 0 < n
    · rw [sourceDiagonalScaledActionRoot,if_pos hn,norm_mul,
        Complex.norm_of_nonneg ((Weight.sobolev (1/2)).positive n).le]
      exact hbound ψ hψ n hn
    · simpa only [sourceDiagonalScaledActionRoot,if_neg hn,norm_zero] using hR
  have hrealize (ψ : CoeffPair 2) (hψ : ψ ∈ U) :
      ∃ b : Coeff ⊤, (∀ n, b n = sourceDiagonalScaledActionRoot n ψ) ∧ ‖b‖ ≤ R := by
    let b : Coeff ⊤ := ⟨fun n => sourceDiagonalScaledActionRoot n ψ,
      memℓp_infty ⟨R,by rintro _ ⟨n,rfl⟩; exact hb ψ hψ n⟩⟩
    exact ⟨b,fun _ => rfl,lp.norm_le_of_forall_le hR (hb ψ hψ)⟩
  obtain ⟨he,hAn⟩ := Coeff.analytic_realization_of_local_bounds
    (fun ψ n => sourceDiagonalScaledActionRoot n ψ) hU hcoord
    (fun ψ hψ => ⟨U,hU,hψ,Subset.rfl,R,hrealize⟩)
  exact ⟨U,hU,hφU,hAn,he⟩

end NLS.ZakharovShabat
