import NLS.KdV.HillHminusOneNormalizedDifferentials
import NLS.SequenceSpaces.HilbertMatrixTransposeAnalytic

/-! # Native Hilbert family of normalized entire Hill numerators

The output index is assembled by the bilinear transpose of the actual
period inverse. This gives one Banach analytic family, with a full Hilbert
norm bound, on the same complex source domain as the constructed inverse.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- The entire normalized numerators assembled in the output-index Hilbert space. -/
def hillHminusNormalizedNumeratorSequence (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (t : ℂ × PeriodOneHminusOne) : Coeff 2 :=
  Coeff.hilbertMatrixTranspose (R t.2) (hillHminusNumeratorHilbert C N t)

/-- Every positive component is the already constructed normalized numerator. -/
theorem hillHminusNormalizedNumeratorSequence_positive (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (t : ℂ × PeriodOneHminusOne) (n : ℕ+) :
    hillHminusNormalizedNumeratorSequence C N R t (n : ℤ) =
      hillHminusNormalizedNumerator C N R n t := by
  change Coeff.hilbertCotangentCoefficients
    ((Coeff.dualPairing (hillHminusNumeratorHilbert C N t)).comp (R t.2)) (n : ℤ) = _
  rw [Coeff.hilbertCotangentCoefficients_apply]
  exact Coeff.dualPairing_hilbert_comm _ _

/-- The bound controls the full output sequence at once. -/
theorem norm_hillHminusNormalizedNumeratorSequence_le (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2)) (t : ℂ × PeriodOneHminusOne) :
    ‖hillHminusNormalizedNumeratorSequence C N R t‖ ≤
      ‖R t.2‖ * ‖hillHminusNumeratorHilbert C N t‖ :=
  Coeff.norm_hilbertMatrixTranspose_apply_le _ _

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

/-- Joint analyticity holds in the native output Hilbert norm on one domain
before all output indices, rather than on separate scalar neighborhoods. -/
theorem normalizedNumeratorSequence_analytic
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2)) (hR : AnalyticOnNhd ℂ R V) :
    AnalyticOnNhd ℂ (hillHminusNormalizedNumeratorSequence C N R) (univ ×ˢ V) := by
  intro t ht
  exact Coeff.analyticAt_hilbertMatrixTranspose_apply
    ((hR t.2 ht.2).comp (f := fun s : ℂ × PeriodOneHminusOne => s.2) analyticAt_snd)
    (D.numeratorHilbert_spec.2 t ht)

/-- In particular, the energy family is entire with values in the output
Hilbert space at every source in the common domain. -/
theorem normalizedNumeratorSequence_entire
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (hR : AnalyticOnNhd ℂ R V) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    AnalyticOnNhd ℂ (fun E : ℂ => hillHminusNormalizedNumeratorSequence C N R (E,q)) univ := by
  intro E _
  exact (D.normalizedNumeratorSequence_analytic R hR (E,q) ⟨mem_univ _,hq⟩).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

/-- A single neighborhood and constant control every output coordinate
and the full output norm near each energy-source point. -/
theorem exists_local_normalizedNumeratorSequence_bound
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2)) (hR : AnalyticOnNhd ℂ R V)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ univ ×ˢ V) :
    ∃ U : Set (ℂ × PeriodOneHminusOne), IsOpen U ∧ t ∈ U ∧ U ⊆ univ ×ˢ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ s ∈ U,
        ‖hillHminusNormalizedNumeratorSequence C N R s‖ ≤ M ∧
        ∀ n : ℕ+, ‖hillHminusNormalizedNumerator C N R n s‖ ≤ M := by
  let F := hillHminusNormalizedNumeratorSequence C N R
  let M := ‖F t‖ + 1
  have ha := D.normalizedNumeratorSequence_analytic R hR
  let U := (univ ×ˢ V) ∩ {s | ‖F s‖ < M}
  have hU : IsOpen U := (ha.continuousOn.norm.isOpen_inter_preimage (isOpen_univ.prod D.isOpen)
    isOpen_Iio)
  have htU : t ∈ U := ⟨ht, by change ‖F t‖ < M; dsimp only [M]; linarith⟩
  refine ⟨U,hU,htU,fun _ hs => hs.1,M,by dsimp only [M]; positivity,?_⟩
  intro s hs
  refine ⟨hs.2.le,?_⟩
  intro n
  rw [← hillHminusNormalizedNumeratorSequence_positive]
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F s) (n : ℤ)).trans hs.2.le

end HillHminusUniformPeriodData
end NLS.KdV
