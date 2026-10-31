import NLS.ComplexAnalysis.LocalAnalyticSquareRoot
import NLS.ZakharovShabat.SourceSymmetricContour

/-! # Analytic branches of an unordered noncollapsed endpoint pair in F.2

Analytic midpoint and squared gap give local branches through both prescribed
endpoints, even at complex sources. The labels themselves need not be continuous.
An arbitrary positive tolerance controls both branches on one neighborhood.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An unordered pair admits analytic branches through its two distinct base values. -/
theorem exists_local_analytic_pair_branches (l r : E → ℂ) (U : Set E) (hU : IsOpen U)
    (a : E) (ha : a ∈ U) (hmid : AnalyticAt ℂ (fun b => (l b+r b)/2) a)
    (hsq : AnalyticAt ℂ (fun b => (r b-l b)^2) a) (hne : l a ≠ r a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ ∃ ρ₁ ρ₂ : E → ℂ,
      AnalyticOnNhd ℂ ρ₁ V ∧ AnalyticOnNhd ℂ ρ₂ V ∧ ρ₁ a = l a ∧ ρ₂ a = r a ∧
      ∀ b ∈ V, ({ρ₁ b,ρ₂ b} : Set ℂ) = {l b,r b} ∧ ρ₁ b ≠ ρ₂ b ∧
        ‖ρ₁ b-l a‖ < ε ∧ ‖ρ₂ b-r a‖ < ε := by
  have hg : r a-l a ≠ 0 := sub_ne_zero.mpr hne.symm
  obtain ⟨S,hS,haS,g,hgA,hga,hgS⟩ :=
    exists_local_analytic_squareRoot (fun b => (r b-l b)^2) a (r a-l a) hsq hg rfl
  let ρ₁ := fun b => (l b+r b)/2-g b/2
  let ρ₂ := fun b => (l b+r b)/2+g b/2
  have hρ₁ : AnalyticAt ℂ ρ₁ a := hmid.sub (hgA a haS).div_const
  have hρ₂ : AnalyticAt ℂ ρ₂ a := hmid.add (hgA a haS).div_const
  have hbase₁ : ρ₁ a = l a := by dsimp [ρ₁]; rw [hga]; ring
  have hbase₂ : ρ₂ a = r a := by dsimp [ρ₂]; rw [hga]; ring
  have hn₁ : ∀ᶠ b in 𝓝 a, ‖ρ₁ b-l a‖ < ε :=
    ((hρ₁.continuousAt.sub continuousAt_const).norm).eventually
      (gt_mem_nhds (by simpa only [Pi.sub_apply,hbase₁,sub_self,norm_zero] using hε))
  have hn₂ : ∀ᶠ b in 𝓝 a, ‖ρ₂ b-r a‖ < ε :=
    ((hρ₂.continuousAt.sub continuousAt_const).norm).eventually
      (gt_mem_nhds (by simpa only [Pi.sub_apply,hbase₂,sub_self,norm_zero] using hε))
  have hUevent : ∀ᶠ b in 𝓝 a, b ∈ U := hU.mem_nhds ha
  have hSevent : ∀ᶠ b in 𝓝 a, b ∈ S := hS.mem_nhds haS
  have hnear := hUevent.and (hSevent.and
    (hρ₁.eventually_analyticAt.and (hρ₂.eventually_analyticAt.and (hn₁.and hn₂))))
  obtain ⟨V,hVsub,hV,haV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨V,hV,haV,fun b hb => (hVsub hb).1,ρ₁,ρ₂,
    (fun b hb => (hVsub hb).2.2.1),(fun b hb => (hVsub hb).2.2.2.1),hbase₁,hbase₂,?_⟩
  intro b hb
  have hbS := (hVsub hb).2.1
  have hpair : ({ρ₁ b,ρ₂ b} : Set ℂ) = {l b,r b} := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hgS b hbS).2 with h | h
    · have h₁ : ρ₁ b = l b := by dsimp [ρ₁]; rw [h]; ring
      have h₂ : ρ₂ b = r b := by dsimp [ρ₂]; rw [h]; ring
      rw [h₁,h₂]
    · have h₁ : ρ₁ b = r b := by dsimp [ρ₁]; rw [h]; ring
      have h₂ : ρ₂ b = l b := by dsimp [ρ₂]; rw [h]; ring
      rw [h₁,h₂,pair_comm]
  have hdistinct : ρ₁ b ≠ ρ₂ b := by
    intro he
    apply (hgS b hbS).1
    dsimp [ρ₁,ρ₂] at he
    linear_combination -he
  exact ⟨hpair,hdistinct,(hVsub hb).2.2.2.2⟩

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every noncollapsed complex pair has local analytic branches on the common symmetric domain. -/
theorem exists_appendixFOpenGapBranches (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ n : ℤ,
        canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0 →
        ∀ ε : ℝ, 0 < ε → ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
          ∃ ρ₁ ρ₂ : CoeffPair p → ℂ,
            AnalyticOnNhd ℂ ρ₁ V ∧ AnalyticOnNhd ℂ ρ₂ V ∧
            ρ₁ φ = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∧
            ρ₂ φ = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∧
            ∀ ψ ∈ V,
              ({ρ₁ ψ,ρ₂ ψ} : Set ℂ) =
                {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
                 canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} ∧
              ρ₁ ψ ≠ ρ₂ ψ ∧
              ‖ρ₁ ψ-canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ < ε ∧
              ‖ρ₂ ψ-canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ < ε := by
  obtain ⟨W,hW,hconn,hr,hA⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W,hW,hconn,hr,?_⟩
  intro φ hφ n hgap ε hε
  exact NLS.ComplexAnalysis.exists_local_analytic_pair_branches
    (fun ψ => canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (fun ψ => canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    W hW φ hφ (hA φ hφ n).1 (hA φ hφ n).2
    (sub_ne_zero.mp hgap).symm ε hε

end NLS.ZakharovShabat
