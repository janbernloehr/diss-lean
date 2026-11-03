import NLS.ZakharovShabat.SourceFiniteGapFourthOpenMoments
import NLS.ZakharovShabat.SourceFiniteGapOpeningHamiltonian

/-! # Actual physical H₄ on a Birkhoff gap-opening line

Fixed finite spectral support gives analytic physical H₂ and H₄ along
the actual amplitude curve. The action t²/2 fixes the frequency's
closed-action normalization without assuming a moment representation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex
namespace NLS.ZakharovShabat

/-- A finite-support analytic source curve has analytic physical momentum. -/
theorem analyticAt_sourceFiniteGapHamiltonian_two_on_curve
    (γ : ℝ → realTypeSourceSubmodule 2)
    (hf : ∀ t, γ t ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ t, ∀ k ∉ S, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (γ t).val) (periodOnePotential_mem (γ t).val) k = 0)
    (t : ℝ) (hγ : AnalyticAt ℝ γ t) :
    AnalyticAt ℝ (fun v => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ v) (hf v) 2) t := by
  obtain ⟨W,U,_,F⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  obtain ⟨R,hR,_,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) (γ t).val S 0
  have hsource : AnalyticAt ℝ (fun v => (γ v).val) t :=
    ((realTypeSourceSubmodule 2).subtypeL.analyticAt _).comp hγ
  have hP := (F.analyticAt_momentumContour 0 R hR.le (γ t).val
    (F.real_subset (γ t).property) hcircle).restrictScalars (𝕜 := ℝ)
  apply (hP.comp (f := fun v => (γ v).val) hsource).congr
  have he := hsource.continuousAt.tendsto.eventually
    (F.eventually_momentumContour_eq_physical_of_gap_support (γ t) S R hR hseg)
  filter_upwards [he] with v hv
  exact hv (γ v).property (hf v) (hS v)

/-- The physical fourth Hamiltonian is analytic on the same source curves. -/
theorem analyticAt_sourceFiniteGapHamiltonian_four_on_curve
    (γ : ℝ → realTypeSourceSubmodule 2)
    (hf : ∀ t, γ t ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ t, ∀ k ∉ S, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (γ t).val) (periodOnePotential_mem (γ t).val) k = 0)
    (t : ℝ) (hγ : AnalyticAt ℝ γ t) :
    AnalyticAt ℝ (fun v => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ v) (hf v) 4) t := by
  obtain ⟨W,U,_,F⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  obtain ⟨R,hR,_,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) (γ t).val S 0
  have hsource : AnalyticAt ℝ (fun v => (γ v).val) t :=
    ((realTypeSourceSubmodule 2).subtypeL.analyticAt _).comp hγ
  have hC := (F.analyticAt_fourthContour 0 R hR.le (γ t).val
    (F.real_subset (γ t).property) hcircle).restrictScalars (𝕜 := ℝ)
  have hM := (analyticOnNhd_sourceHilbertMass (γ t).val (mem_univ _)).restrictScalars (𝕜 := ℝ)
  have hP := analyticAt_sourceFiniteGapHamiltonian_two_on_curve γ hf S hS t hγ
  have hG : AnalyticAt ℝ (fun v => sourceFullAbelianFourthContour (by simp) (by norm_num) W 0 R (γ v).val+
      6*((sourceHilbertMass (γ v).val)*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ v) (hf v) 2)) t :=
    (hC.comp (f := fun v => (γ v).val) hsource).add
      (analyticAt_const.mul ((hM.comp (f := fun v => (γ v).val) hsource).mul hP))
  apply hG.congr
  have he := hsource.continuousAt.tendsto.eventually
    (F.eventually_fourthContour_eq_physical_of_gap_support (γ t) S R hR hseg)
  filter_upwards [he] with v hv
  have hval := hv (γ v).property (hf v) (hS v)
  rw [sourceFiniteGapNLSHamiltonian_one_eq_mass] at hval
  linear_combination hval

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Physical H₄ is analytic even at the collapsed opening amplitude. -/
theorem analyticOnNhd_physicalGapOpeningHamiltonian_four
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    AnalyticOnNhd ℝ (D.physicalGapOpeningHamiltonian φ hf n 4) univ := by
  classical
  intro t _
  exact analyticAt_sourceFiniteGapHamiltonian_four_on_curve (D.hilbertGapOpening φ n)
    (D.hilbertGapOpening_mem_finiteGap φ hf n) (insert n hf.toFinset)
    (D.hilbertGapOpening_gap_support φ hf n) t
    (D.analyticOnNhd_hilbertGapOpening φ n t (mem_univ _))

/-- The amplitude derivative equals amplitude times the independently defined
physical open-action frequency, using the exact action t²/2. -/
theorem deriv_physicalGapOpeningHamiltonian_four
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) (t : ℝ) (ht : t ≠ 0) :
    deriv (D.physicalGapOpeningHamiltonian φ hf n 4) t =
      (t:ℂ)*D.finiteGapFourthOpenFrequency (D.hilbertGapOpening φ n t)
        (D.hilbertGapOpening_mem_finiteGap φ hf n t) n (D.hilbertGapOpening_gap_ne_zero φ n hn t ht) := by
  let H := D.physicalGapOpeningHamiltonian φ hf n 4
  let q := fun u : ℝ => t*RealCoeff.actionReductionScale (t^2/2) u
  have hq0 : q 0 = t := by simp [q,RealCoeff.actionReductionScale]
  have hq : HasDerivAt q (-1/t) 0 := by
    have hsq := (((hasDerivAt_id (0:ℝ)).div_const (t^2/2)).const_sub 1).sqrt (by norm_num)
    convert! hsq.const_mul t using 1
    norm_num
    field_simp
  have hH : HasDerivAt H (deriv H t) (q 0) := by
    rw [hq0]
    exact (D.analyticOnNhd_physicalGapOpeningHamiltonian_four φ hf n t (mem_univ _)).differentiableAt.hasDerivAt
  have hd := (hH.scomp 0 hq).deriv
  have heq : (fun u => H (q u)) = D.physicalActionReductionHamiltonian (D.hilbertGapOpening φ n t)
      (D.hilbertGapOpening_mem_finiteGap φ hf n t) n 4 := by
    funext u
    exact (D.physicalActionReductionHamiltonian_gapOpening φ hf n hn 4 t u).symm
  change deriv (fun u => H (q u)) 0 = (-1/t) • deriv H t at hd
  rw [heq] at hd
  dsimp only [finiteGapFourthOpenFrequency]
  rw [hd,Complex.real_smul]
  change deriv H t = (t:ℂ)*(-(((-1/t:ℝ):ℂ)*deriv H t))
  push_cast
  field_simp [show (t:ℂ) ≠ 0 by exact_mod_cast ht]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
