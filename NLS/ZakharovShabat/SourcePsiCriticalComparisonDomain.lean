import NLS.ZakharovShabat.SourceCriticalRelativeComparison

/-! # A constructed common domain for the actual root comparison

Neither zero-period assumptions nor a free numerator family are inputs.
The canonical psi family, the critical periods and all valid comparison
circles are constructed from existing spectral results. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (38) holds for the actual root family on an open neighborhood of all real sources.
The deleted critical root is separated from the selected circle, including collapsed gaps. -/
theorem exists_sourcePsi_critical_comparison (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceTheorem12_1Data hp hp1 W₀ W s ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
        ∀ ψ ∈ U, ∃ c : ℝ, 1 ≤ c ∧ ∀ n k : ℤ, k ≠ n →
          ∃ P : SourceCriticalRootPeriodCircle hp hp1 ψ k,
            sourceCriticalRoot hp hp1 ψ n ≠ sourceCriticalRoot hp hp1 ψ k ∧
            (∀ z ∈ sphere (P.center : ℂ) P.radius, sourceCriticalRoot hp hp1 ψ n-z ≠ 0) ∧
            SourcePsiCriticalComparisonIdentity hp hp1 n k (s n ψ) ψ (P.center : ℂ) P.radius ∧
            ∀ z ∈ closedBall (P.center : ℂ) P.radius,
              SourcePsiCriticalRelativeEstimate hp hp1 n k (s n ψ) ψ z c := by
  obtain ⟨W₀,_,_,_,W,hW,_,hrealW,s,H⟩ := sourceTheorem12_1 hp hp1
  obtain ⟨C,hC,_,hrealC,K⟩ := sourceLemma10_11CirclePeriods hp hp1
  obtain ⟨Q,hQ,_,hrealQ,hquot⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  obtain ⟨I,hI,_,hrealI,hisol⟩ := sourceLemma10_1 hp hp1
  let U := W ∩ (C ∩ (Q ∩ I))
  refine ⟨W₀,W,s,H,U,hW.inter (hC.inter (hQ.inter hI)),?_,inter_subset_left,?_⟩
  · intro ψ hψ
    exact ⟨hrealW hψ,hrealC hψ,hrealQ hψ,hrealI hψ⟩
  intro ψ hψ
  obtain ⟨V,_,_,hψV,_,φ,_,N,ε,_,_,c,hD⟩ := hisol ψ hψ.2.2.2
  refine ⟨c,hD.one_le,?_⟩
  intro n k hkn
  obtain ⟨a,r,hr,he⟩ := hD.discs k
  let P := hD.periodCircle ψ hψV k a r hr he
  have hcrit (j : ℤ) : sourceCriticalRoot hp hp1 ψ j ∈ sourceIsolatingDisc hp hp1 φ N ε j :=
    hD.cluster ψ hψV j (by
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hsep : sourceCriticalRoot hp hp1 ψ n ≠ sourceCriticalRoot hp hp1 ψ k :=
    (hD.disjoint n k hkn.symm).ne_of_mem (hcrit n) (hcrit k)
  have hd := (hD.disjoint n k hkn.symm).closure_right
    (isOpen_sourceIsolatingDisc hp hp1 φ N ε n)
  have havoid : ∀ z ∈ sphere (P.center : ℂ) P.radius, sourceCriticalRoot hp hp1 ψ n-z ≠ 0 := by
    intro z hz hnz
    have hzcl : z ∈ closure (sourceIsolatingDisc hp hp1 φ N ε k) := by
      rw [he,closure_ball _ hr.ne']
      exact sphere_subset_closedBall hz
    have hν := hcrit n
    rw [sub_eq_zero.mp hnz] at hν
    exact Set.disjoint_left.mp hd hν hzcl
  refine ⟨P,hsep,havoid,?_,?_⟩
  · exact H.psi_critical_root_comparison K (fun j => (hquot j).2) ψ hψ.1 hψ.2.1 hψ.2.2.1 n k hkn P havoid
  · intro z hz
    have hzcl : z ∈ closure (sourceIsolatingDisc hp hp1 φ N ε k) := by
      rw [he,closure_ball _ hr.ne']
      exact hz
    exact hD.norm_psiFilledQuotient_sub_critical_le ψ hψV n k (s n ψ) z hzcl
end NLS.ZakharovShabat
