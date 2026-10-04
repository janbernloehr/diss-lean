import NLS.ZakharovShabat.SourceAbelianMomentDomain

/-! # Lemma 20.1 for actual normalized moments

All four clauses hold on one open simply connected neighborhood of the
entire real source locus, at every finite Banach exponent above one.
The moments are represented by actual primitive/psi contour integrals;
all orders and both indices share the same local isolating circles.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Source-space Lemma 20.1, with the actual normalized psi extension
and a simultaneous contour representation of every moment. -/
theorem exists_sourceAbelianMoment_lemma20_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V U : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      IsOpen U ∧ IsSimplyConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiNormalizedComplexExtension hp hp1 V s ∧
        ∃ Ω : ℤ → ℤ → ℕ → CoeffPair p → ℂ,
          (∀ (n k : ℤ) (m : ℕ), AnalyticOnNhd ℂ (Ω n k m) U) ∧
          (∀ ψ ∈ U, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
            sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
            ∀ (n k : ℤ) (m : ℕ), Ω n k m ψ =
              sourceAbelianMomentCircle hp hp1 W n k m (s n ψ : Coeff p) ψ (c k) (R k)) ∧
          (∀ ψ ∈ U, ∀ n k : ℤ, Ω n k 0 ψ = (2*Real.pi : ℂ)*(if k = n then 1 else 0)) ∧
          (∀ ψ ∈ U, ∀ (n k : ℤ) (l : ℕ), Ω n k (2*l+1) ψ = 0) ∧
          (∀ ψ ∈ U, ∀ n k : ℤ,
            canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0 →
            ∀ m : ℕ, 1 ≤ m → Ω n k m ψ = 0) := by
  classical
  obtain ⟨W,V,hW,hrealW,hV,hrealV,s,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts hp hp1
  choose L hLV using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 W s := ⟨L⟩
  have hUV : A.domain ⊆ V := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hLV φ hφ
  refine ⟨W,V,A.domain,hW,hrealW,hV,hrealV,A.isOpen_domain,A.isSimplyConnected_domain,
    A.realType_subset_domain,hUV,s,hs,A.moment,A.analytic_moment,A.circle_representation,
    A.moment_zero_order,A.moment_odd,?_⟩
  intro ψ hψ n k hgap m hm
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact A.moment_succ_of_collapsed ψ hψ n k hgap l

end NLS.ZakharovShabat
