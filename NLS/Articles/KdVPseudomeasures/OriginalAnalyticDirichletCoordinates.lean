import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActionQuotients
import NLS.Articles.KdVPseudomeasures.OriginalDirichletLabels
import NLS.KdV.HminusOneCanonicalDirichletAsymptotics

/-! # Actual original Dirichlet energies for the KdV angle construction

Every original real Dirichlet label lies in its SAME original periodic
gap, including all low and collapsed gaps. ONE common connected complex
neighborhood supports ALL simple analytic Dirichlet energies and the
previous canonical actions, squared gaps and nonzero quotients. The
Dirichlet energies exhaust the full native spectrum with exact physical
algebraic multiplicities. This constructs the divisor's ENERGY coordinate;
its actual norming sheet, normalized Hill differentials and KdV angles
and Birkhoff coordinates remain separate essential obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem originalDirichletLabels_mem_gap (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalHillLabels q (2*(n : ℕ)-1) ≤ originalDirichletLabels q n ∧
      originalDirichletLabels q n ≤ originalHillLabels q (2*(n : ℕ)) :=
  hillHminusDirichletLabels_mem_gap _ _ n

theorem norm_originalDirichletLabels_sub_midpoint_le_half_gap
    (q : OriginalHminusOnePotential) (n : ℕ+) :
    ‖(originalDirichletLabels q n : ℂ)-
      (((originalHillLabels q (2*(n : ℕ)-1)+originalHillLabels q (2*(n : ℕ)))/2 : ℝ) : ℂ)‖ ≤
      ‖((originalHillLabels q (2*(n : ℕ))-originalHillLabels q (2*(n : ℕ)-1) : ℝ) : ℂ)‖/2 :=
  norm_hillHminusDirichletLabels_sub_midpoint_le_half_gap _ _ n

theorem originalDirichletLabels_eq_endpoint_of_gap_zero
    (q : OriginalHminusOnePotential) (n : ℕ+)
    (hg : originalCanonicalGapValues q (n : ℕ) = 0) :
    originalDirichletLabels q n = originalHillLabels q (2*(n : ℕ)-1) := by
  have hn : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hg' : ((originalHillLabels q (2*(n : ℕ))-originalHillLabels q (2*(n : ℕ)-1) : ℝ) : ℂ) = 0 := by
    simpa only [originalCanonicalGapValues,if_neg hn,Int.natAbs_natCast] using hg
  exact hillHminusDirichletLabels_eq_endpoint_of_gap_zero _ _ n (ofReal_eq_zero.mp hg')

theorem originalCanonicalDirichlet_eq (q : OriginalHminusOnePotential) (n : ℕ+) :
    hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q) = (originalDirichletLabels q n : ℂ) :=
  hillHminusCanonicalDirichlet_eq_real _ (originalPeriodOneCoefficients_real q) n

theorem exists_originalKdV_common_analytic_Dirichlet_data :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalActionQuotient n) W ∧
        ∀ a ∈ W, hillHminusDirichlet a (hillHminusCanonicalDirichlet n a) = 0 ∧
          deriv (hillHminusDirichlet a) (hillHminusCanonicalDirichlet n a) ≠ 0 ∧
          singularDirichletAlgebraicMultiplicity (periodOneOriginal a) (hillHminusCanonicalDirichlet n a) = 1 ∧
          hillHminusCanonicalActionQuotient n a ≠ 0) ∧
      ∀ a ∈ W, Function.Injective (fun n : ℕ+ => hillHminusCanonicalDirichlet n a) ∧
        Memℓp (fun n : ℕ+ => (hillHminusCanonicalDirichlet n a-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℕ)) 2 ∧
        ∀ energy : ℂ,
          (energy ∈ singularDirichletSpectrum (periodOneOriginal a) ↔
            ∃ n : ℕ+, energy = hillHminusCanonicalDirichlet n a) ∧
          (∑ᶠ n : ℕ+, if hillHminusCanonicalDirichlet n a = energy then (1 : ℕ) else 0) =
            singularDirichletAlgebraicMultiplicity (periodOneOriginal a) energy := by
  refine ⟨hillHminusCanonicalDirichletDomain,isOpen_hillHminusCanonicalDirichletDomain,
    isConnected_hillHminusCanonicalDirichletDomain,
    (fun q => real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q)),?_,?_⟩
  · intro n
    refine ⟨analyticOnNhd_hillHminusCanonicalDirichlet n,
      (analyticOnNhd_hillHminusCanonicalAction_on_ratioDomain n).mono hillHminusCanonicalDirichletDomain_subset,
      (analyticOnNhd_hillHminusCanonicalGapSquare_on_ratioDomain n).mono hillHminusCanonicalDirichletDomain_subset,
      (analyticOnNhd_hillHminusCanonicalActionQuotient n).mono hillHminusCanonicalDirichletDomain_subset,?_⟩
    intro a ha
    exact ⟨hillHminusCanonicalDirichlet_is_root n a ha,deriv_hillHminusCanonicalDirichlet_ne_zero n a ha,
      hillHminusCanonicalDirichlet_native_multiplicity n a ha,
      hillHminusCanonicalActionQuotient_ne_zero n a (hillHminusCanonicalDirichletDomain_subset ha)⟩
  · intro a ha
    exact ⟨injective_hillHminusCanonicalDirichlet a ha,memlp_hillHminusCanonicalDirichlet_inverseIndex_error a ha,
      fun energy => ⟨hillHminusCanonicalDirichlet_spectrum_iff a ha energy,
        hillHminusCanonicalDirichlet_global_multiplicity a ha energy⟩⟩

end NLS.Articles.KdVPseudomeasures
