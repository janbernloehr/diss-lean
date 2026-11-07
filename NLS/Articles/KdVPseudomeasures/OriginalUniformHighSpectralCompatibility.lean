import NLS.Articles.KdVPseudomeasures.OriginalHighPairCompatibility
import NLS.Articles.KdVPseudomeasures.SpectralComplexCanonical
import NLS.Articles.KdVPseudomeasures.ComplexMidpointEstimate
import NLS.KdV.HillCanonicalHighSymmetricComparison
import NLS.KdV.HillCanonicalCartesianWeight
import NLS.RealAnalysis.SqrtSublinearLattice

/-! A common native complex neighborhood and original norm-ball cutoff
identify all sufficiently high intrinsic gap/midpoint/Dirichlet quantities
with the ACTUAL original endpoint labels. No reality of nearby sources or
nonvanishing of their gaps is assumed. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_uniform_original_high_canonical_spectral_comparison
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (a : PeriodOneHminusOne) (har : IsRealPeriodOneHminusOne a) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ a ∈ U ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, sourceNativePeriodOneCLM r hr q ∈ U →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        hillHminusCanonicalGapSquare n (sourceNativePeriodOneCLM r hr q)=
          (sourceHillComplexLabels r hr q (2*(n:ℕ))-sourceHillComplexLabels r hr q (2*(n:ℕ)-1))^2 ∧
        hillHminusCanonicalEnergyMidpoint n (sourceNativePeriodOneCLM r hr q)=
          (sourceHillComplexLabels r hr q (2*(n:ℕ)-1)+sourceHillComplexLabels r hr q (2*(n:ℕ)))/2 ∧
        hillHminusCanonicalDirichlet n (sourceNativePeriodOneCLM r hr q)=
          originalComplexDirichletLabels (sourceOriginalComplexPotential r hr q hp) n := by
  obtain ⟨rho,NC,V,hrho,hrhop,hNC,hV,haV,_,hcanonical⟩ := exists_common_canonical_high_symmetric_comparison a har
  obtain ⟨ND,W,_,hW,haW,_,hDirichlet⟩ := exists_hillHminusCanonicalDirichlet_uniform_high_comparison a
    (real_mem_hillHminusCanonicalDirichletDomain a har)
  obtain ⟨NL,_,hlabel⟩ := source_uniform_canonical_complex_labels r hr R
  obtain ⟨NS,_,hsmall⟩ := NLS.RealAnalysis.exists_nat_sqrt_div_four_lt_linear (Real.pi*rho) (mul_pos Real.pi_pos hrho)
  let N := max NC (max ND (max NL NS))
  refine ⟨N,V ∩ W,hNC.trans (le_max_left _ _),hV.inter hW,⟨haV,haW⟩,?_⟩
  intro q hq hp hqU n hn
  have hnC : NC ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnD : ND ≤ (n:ℕ) := by dsimp [N] at hn; omega
  have hnL : NL ≤ (n:ℕ) := by dsimp [N] at hn; omega
  have hnS : NS ≤ (n:ℕ) := by dsimp [N] at hn; omega
  obtain ⟨p,hl,hu⟩ := (hlabel q hq).high_pair (n:ℕ) hnL
  obtain ⟨l,u,hpair,htau,hgap⟩ := hcanonical n hnC _ hqU.1
  have hloc : Real.sqrt (n:ℝ)/4 < Real.pi*(n:ℝ)*rho := by
    have h := hsmall (n:ℕ) hnS
    convert h using 1; ring
  have he := p.eq_or_swap_native_high_pair r hr q hp n rho hrhop l u hpair hloc
  have hperiod : hillHminusCanonicalGapSquare n (sourceNativePeriodOneCLM r hr q)=
      (p.right-p.left)^2 ∧
      hillHminusCanonicalEnergyMidpoint n (sourceNativePeriodOneCLM r hr q)=(p.left+p.right)/2 := by
    rw [htau,hgap]
    rcases he with h | h <;> rw [h.1,h.2] <;> constructor <;> ring
  refine ⟨?_,?_,?_⟩
  · rw [hl,hu]
    exact hperiod.1
  · rw [hl,hu]
    exact hperiod.2
  · exact hDirichlet n hnD hqU.2

theorem exists_uniform_original_high_canonical_weight_comparison
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (a : PeriodOneHminusOne) (har : IsRealPeriodOneHminusOne a) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ a ∈ U ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, sourceNativePeriodOneCLM r hr q ∈ U →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        hillHminusCanonicalCartesianWeight n (sourceNativePeriodOneCLM r hr q)=
          ‖sourceComplexCanonicalGapValues r hr q (n:ℤ)‖+‖sourceComplexDirichletMidpoint r hr q hp n‖ := by
  obtain ⟨N,U,hN,hU,haU,hcompare⟩ := exists_uniform_original_high_canonical_spectral_comparison r hr R a har
  refine ⟨N,U,hN,hU,haU,?_⟩
  intro q hq hp hqU n hn
  obtain ⟨hgap,htau,hmu⟩ := hcompare q hq hp hqU n hn
  rw [hillHminusCanonicalCartesianWeight,hgap,htau,hmu,norm_pow,Real.sqrt_sq (norm_nonneg _)]
  have hn0 : (n:ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [sourceComplexCanonicalGapValues,if_neg hn0,Int.natAbs_natCast,sourceComplexDirichletMidpoint]
  congr 1
  rw [norm_sub_rev,add_comm]

end NLS.Articles.KdVPseudomeasures
