import NLS.ZakharovShabat.SourceHilbertGapOpening
import NLS.ZakharovShabat.SourceFiniteGapOpenFrequency

/-! # Analytic physical Hamiltonians on a gap-opening line

Fixed finite gap support permits a single local contour at every parameter.
Thus the physical third Hamiltonian, not just a surrogate contour, is real
analytic along the entire Birkhoff amplitude line, including zero amplitude.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ZakharovShabat

/-- A real analytic source curve with fixed finite gap support has a real
analytic physical third Hamiltonian. No Sobolev convergence is assumed. -/
theorem analyticAt_sourceFiniteGapHamiltonian_three_on_curve
    (γ : ℝ → realTypeSourceSubmodule 2)
    (hf : ∀ t, γ t ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ t, ∀ k ∉ S, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (γ t).val) (periodOnePotential_mem (γ t).val) k = 0)
    (t : ℝ) (hγ : AnalyticAt ℝ γ t) :
    AnalyticAt ℝ (fun v => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ v) (hf v) 3) t := by
  obtain ⟨W,U,_,F⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  obtain ⟨R,hR,_,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) (γ t).val S 0
  have hsource : AnalyticAt ℝ (fun v => (γ v).val) t :=
    ((realTypeSourceSubmodule 2).subtypeL.analyticAt _).comp hγ
  have hC := (F.analyticAt_cubicContour 0 R hR.le (γ t).val
    (F.real_subset (γ t).property) hcircle).restrictScalars (𝕜 := ℝ)
  have hM := (analyticOnNhd_sourceHilbertMass (γ t).val (mem_univ _)).restrictScalars (𝕜 := ℝ)
  have hG : AnalyticAt ℝ (fun v => sourceFullAbelianCubicContour (by simp) (by norm_num) W 0 R (γ v).val +
      2*(sourceHilbertMass (γ v).val)^2) t :=
    (hC.comp (f := fun v => (γ v).val) hsource).add
      (analyticAt_const.mul ((hM.comp (f := fun v => (γ v).val) hsource).pow 2))
  apply hG.congr
  have he := hsource.continuousAt.tendsto.eventually
    (F.eventually_cubicContour_eq_physical_of_gap_support (γ t) S R hR hseg)
  filter_upwards [he] with v hv
  have hval := hv (γ v).property (hf v) (hS v)
  rw [sourceFiniteGapNLSHamiltonian_one_eq_mass] at hval
  linear_combination hval

private theorem physicalHamiltonian_congr
    (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (j : ℕ) (h : φ = ψ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf j =
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) ψ hg j := by
  subst ψ
  rfl

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

def physicalGapOpeningHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (j : ℕ) (t : ℝ) : ℂ :=
  sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (D.hilbertGapOpening φ n t)
    (D.hilbertGapOpening_mem_finiteGap φ hf n t) j

/-- Physical `H3` is analytic even at the collapsed amplitude. -/
theorem analyticOnNhd_physicalGapOpeningHamiltonian_three
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    AnalyticOnNhd ℝ (D.physicalGapOpeningHamiltonian φ hf n 3) univ := by
  classical
  intro t _
  exact analyticAt_sourceFiniteGapHamiltonian_three_on_curve (D.hilbertGapOpening φ n)
    (D.hilbertGapOpening_mem_finiteGap φ hf n) (insert n hf.toFinset)
    (D.hilbertGapOpening_gap_support φ hf n) t
    (D.analyticOnNhd_hilbertGapOpening φ n t (mem_univ _))

/-- The hierarchy on a reduction curve through an opened source is exactly
the hierarchy on the opening line at the reduced amplitude. -/
theorem physicalActionReductionHamiltonian_gapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) (j : ℕ) (t u : ℝ) :
    D.physicalActionReductionHamiltonian (D.hilbertGapOpening φ n t)
      (D.hilbertGapOpening_mem_finiteGap φ hf n t) n j u =
    D.physicalGapOpeningHamiltonian φ hf n j (t*RealCoeff.actionReductionScale (t^2/2) u) := by
  exact physicalHamiltonian_congr _ _ _ _ j (D.hilbertActionReduction_gapOpening φ n hn t u)

/-- Away from zero, the amplitude derivative is amplitude times the actual
open-action frequency. This fixes the normalization for the closed-gap limit. -/
theorem deriv_physicalGapOpeningHamiltonian_three
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) (t : ℝ) (ht : t ≠ 0) :
    deriv (D.physicalGapOpeningHamiltonian φ hf n 3) t =
      (t : ℂ)*D.finiteGapOpenFrequency (D.hilbertGapOpening φ n t)
        (D.hilbertGapOpening_mem_finiteGap φ hf n t) n (D.hilbertGapOpening_gap_ne_zero φ n hn t ht) := by
  let H := D.physicalGapOpeningHamiltonian φ hf n 3
  let q := fun u : ℝ => t*RealCoeff.actionReductionScale (t^2/2) u
  have hq0 : q 0 = t := by simp [q,RealCoeff.actionReductionScale]
  have hq : HasDerivAt q (-1/t) 0 := by
    have hsq := (((hasDerivAt_id (0 : ℝ)).div_const (t^2/2)).const_sub 1).sqrt (by norm_num)
    convert! hsq.const_mul t using 1
    norm_num
    field_simp
  have hH : HasDerivAt H (deriv H t) (q 0) := by
    rw [hq0]
    exact (D.analyticOnNhd_physicalGapOpeningHamiltonian_three φ hf n t (mem_univ _)).differentiableAt.hasDerivAt
  have hd := (hH.scomp 0 hq).deriv
  have heq : (fun u => H (q u)) = D.physicalActionReductionHamiltonian (D.hilbertGapOpening φ n t)
      (D.hilbertGapOpening_mem_finiteGap φ hf n t) n 3 := by
    funext u
    exact (D.physicalActionReductionHamiltonian_gapOpening φ hf n hn 3 t u).symm
  change deriv (fun u => H (q u)) 0 = (-1/t) • deriv H t at hd
  rw [heq] at hd
  dsimp only [finiteGapOpenFrequency]
  rw [hd]
  rw [Complex.real_smul]
  change deriv H t = (t : ℂ)*(-(((-1/t : ℝ) : ℂ)*deriv H t))
  push_cast
  field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ht]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
