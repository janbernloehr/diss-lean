import NLS.ZakharovShabat.SourceFloquetGapOpening
import NLS.ZakharovShabat.SourceRealActionLocalOverlap
import NLS.ZakharovShabat.SourceRealTypeFiniteApproximation
import NLS.SequenceSpaces.FiniteSourceCoefficients

/-! # Nontrivial Floquet gap-opening functions at every exponent

The nonzero Hilbert root bracket rules out vanishing on all finite real
Fourier potentials. Such a finite witness represents the same spectral
function at every finite exponent above one.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A finite real Fourier source witnesses nontriviality at each index.
The proof uses the actual root/Floquet bracket, including at zero source. -/
theorem exists_finite_real_sourceFloquetGapOpening_ne_zero (n : ℤ) :
    ∃ φ : CoeffPair 2, IsRealType (CoeffPair.toMax 2 φ) ∧
      Coeff.HasFiniteSupport φ.fst ∧ Coeff.HasFiniteSupport φ.snd ∧
        sourceFloquetGapOpening (by simp) (by norm_num) n φ ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let F := sourceFloquetGapOpening (p := 2) (by simp) (by norm_num) n
  have hreal0 : IsRealType (CoeffPair.toMax 2 (0 : CoeffPair 2)) := by simp
  have hF := analyticAt_sourceFloquetGapOpening_of_realType (by simp) (by norm_num) n 0 hreal0
  obtain ⟨V,hVsub,hV,h0V⟩ := _root_.mem_nhds_iff.mp hF.eventually_analyticAt
  have hA : AnalyticOnNhd ℂ F V := fun ψ hψ => hVsub hψ
  have hzero (ψ : CoeffPair 2) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax 2 ψ)) : F ψ = 0 :=
    eq_of_continuousOn_of_finite_realType (by simp) hV hA.continuousOn 0
      (fun χ _ hχ hleft hright => h χ hχ hleft hright) ψ hψ hreal
  obtain ⟨U,hU,h0U,_,heq⟩ := exists_local_eqOn_of_eqOn_realType (by simp) 0 hreal0
    V V hV hV h0V h0V F (fun _ => 0) hA.differentiableOn (differentiableOn_const 0)
      (fun ψ hψ hreal => hzero ψ hψ.1 hreal)
  have hlocal : F =ᶠ[𝓝 (0 : CoeffPair 2)] (fun _ => 0) :=
    Filter.eventually_of_mem (hU.mem_nhds h0U) heq
  have hderiv : fderiv ℂ F 0 = 0 := by rw [hlocal.fderiv_eq]; simp
  have hbracket := sourceBracket_boundaryRoot_gapOpening (p := 2) (by simp) (by norm_num) (by norm_num) n 0 hreal0
  change sourceBivector (p := 2) (by norm_num)
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) 0)
      (fderiv ℂ F 0) = _ at hbracket
  rw [hderiv,map_zero] at hbracket
  have hz : sourceBoundaryFloquetMultiplier (by simp) (by norm_num) .dirichlet n (0 : CoeffPair 2) = 0 :=
    sq_eq_zero_iff.mp (neg_eq_zero.mp hbracket.symm)
  exact sourceBoundaryFloquetMultiplier_ne_zero (by simp) (by norm_num) .dirichlet n 0 hz

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Floquet opening function is nontrivial on the real source space
at every finite exponent above one, including below the Hilbert exponent. -/
theorem exists_real_sourceFloquetGapOpening_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ φ : realTypeSourceSubmodule p, sourceFloquetGapOpening hp hp1 n φ.val ≠ 0 := by
  classical
  obtain ⟨ψ,hψ,hleft,hright,hne⟩ := exists_finite_real_sourceFloquetGapOpening_ne_zero n
  obtain ⟨S,hS⟩ := hleft
  obtain ⟨T,hT⟩ := hright
  let a : ℤ →₀ ℂ := Finsupp.onFinset S ψ.fst (fun j hj => by by_contra h; exact hj (hS j h))
  let b : ℤ →₀ ℂ := Finsupp.onFinset T ψ.snd (fun j hj => by by_contra h; exact hj (hT j h))
  let φ : CoeffPair p := CoeffPair.ofFinsupp (a,b)
  have hφreal : IsRealType (CoeffPair.toMax p φ) := fun j => hψ j
  have hψeq : CoeffPair.ofFinsupp (p := 2) (a,b) = ψ := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext j <;> rfl
  refine ⟨⟨φ,hφreal⟩,?_⟩
  by_cases hp2 : p ≤ 2
  · have heq := sourceFloquetGapOpening_exponent hp (show (2 : ℝ≥0∞) ≠ ⊤ by simp) hp1 (by norm_num) hp2 n φ
    dsimp only [φ] at heq
    rw [CoeffPair.exponentInclusion_ofFinsupp,hψeq] at heq
    rw [heq]; exact hne
  · have h2p : (2 : ℝ≥0∞) ≤ p := le_of_not_ge hp2
    have heq := sourceFloquetGapOpening_exponent (show (2 : ℝ≥0∞) ≠ ⊤ by simp) hp (by norm_num) hp1 h2p n
      (CoeffPair.ofFinsupp (p := 2) (a,b))
    rw [CoeffPair.exponentInclusion_ofFinsupp,hψeq] at heq
    rw [← heq]; exact hne

end NLS.ZakharovShabat
