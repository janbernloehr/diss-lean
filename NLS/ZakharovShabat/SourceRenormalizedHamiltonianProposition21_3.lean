import NLS.ZakharovShabat.SourceRenormalizedHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapDensity

/-! # Proposition 21.3: the cubic-moment Hamiltonian extension

A constructed primitive atlas supplies the analytic source extension,
absolute and locally uniform convergence, the strict real zero criterion,
and agreement with the physical finite-gap correction. Finite-gap density
also gives uniqueness among continuous real-source extensions.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
namespace SourcePrimitivePowerAtlas
variable {W V : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- The restriction is real analytic on the full real FL⁴ space. -/
theorem real_renormalizedHamiltonian_analytic :
    AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule 4 => A.renormalizedHamiltonian φ.val) univ := by
  obtain ⟨U,_,_,hreal,_,ha,_,_⟩ := A.exists_renormalizedHamiltonian_analytic
  intro φ _
  exact ((ha φ.val (hreal φ.property)).restrictScalars (𝕜 := ℝ)).comp
    ((realTypeSourceSubmodule 4).subtypeL.analyticAt φ)

/-- The extension is independent of the moment atlas on complex overlaps. -/
theorem renormalizedHamiltonian_eqOn
    (B : SourcePrimitivePowerAtlas (by simp) (by norm_num) V) :
    EqOn A.renormalizedHamiltonian B.renormalizedHamiltonian (A.domain ∩ B.domain) := by
  intro ψ hψ
  unfold renormalizedHamiltonian
  congr 1
  exact tsum_congr (fun n => A.moment_eqOn B n 3 hψ)

/-- Physical finite-gap values determine at most one continuous extension
on all real FL⁴ sources. -/
theorem real_renormalizedHamiltonian_unique
    (H : realTypeSourceSubmodule 4 → ℂ) (hH : Continuous H)
    (hfinite : ∀ (φ : realTypeSourceSubmodule 4) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)),
      H φ = sourceFiniteGapRenormalizedHamiltonian (by simp) (by norm_num) φ hf) :
    H = fun φ => A.renormalizedHamiltonian φ.val := by
  funext φ
  apply sub_eq_zero.mp
  exact eq_of_continuousOn_of_sourceFiniteGap (by simp) (by norm_num) isOpen_univ
    (hH.continuousOn.sub A.real_renormalizedHamiltonian_analytic.continuousOn) 0
    (fun ψ _ hf => sub_eq_zero.mpr ((hfinite ψ hf).trans (A.renormalizedHamiltonian_eq_finiteGap ψ hf).symm))
    φ (mem_univ φ)

end SourcePrimitivePowerAtlas

/-- The source-space Hamiltonian extension of Proposition 21.3,
constructed from actual moments with no supplied existence premises. -/
theorem exists_sourceRenormalizedHamiltonian_proposition21_3 :
    ∃ W U : Set (CoeffPair 4), IsOpen W ∧ IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 4 ⊆ U ∧
      ∃ A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W, U ⊆ A.domain ∧
        AnalyticOnNhd ℂ A.renormalizedHamiltonian U ∧
        (∀ ψ ∈ U, Summable (fun n => ‖A.moment n 3 ψ‖)) ∧
        TendstoLocallyUniformlyOn
          (fun (N : ℕ) ψ => -(4/3:ℂ)*(∑ n ∈ Finset.Icc (-(N:ℤ)) N, A.moment n 3 ψ))
          A.renormalizedHamiltonian atTop U ∧
        AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule 4 => A.renormalizedHamiltonian φ.val) univ ∧
        (∀ φ : realTypeSourceSubmodule 4,
          (A.renormalizedHamiltonian φ.val).re ≤ 0 ∧ (A.renormalizedHamiltonian φ.val).im = 0) ∧
        (∀ φ : realTypeSourceSubmodule 4, A.renormalizedHamiltonian φ.val = 0 ↔ φ = 0) ∧
        (∀ (φ : realTypeSourceSubmodule 4) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)),
          A.renormalizedHamiltonian φ.val = sourceFiniteGapRenormalizedHamiltonian (by simp) (by norm_num) φ hf) := by
  obtain ⟨W,hW,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 4) (by simp) (by norm_num)
  obtain ⟨U,hU,hconn,hreal,hsub,ha,hs,hconv⟩ := A.exists_renormalizedHamiltonian_analytic
  exact ⟨W,U,hW,hU,hconn,hreal,A,hsub,ha,hs,hconv,A.real_renormalizedHamiltonian_analytic,
    A.real_renormalizedHamiltonian_nonpos,A.real_renormalizedHamiltonian_eq_zero_iff,
    A.renormalizedHamiltonian_eq_finiteGap⟩

end NLS.ZakharovShabat
