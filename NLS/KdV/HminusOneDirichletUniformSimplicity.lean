import NLS.KdV.HminusOneDirichletUniformControl
import NLS.KdV.SingularDirichletNormalizedEigenfunction

/-! The complex Dirichlet input to source Section 2.5: ONE original H^-1
neighborhood and cutoff give all simple analytic high labels, with actual
native eigenfunctions normalized in the original physical interval L2 norm. -/
noncomputable section
open Set Complex
namespace NLS.KdV
open NLS.Fourier

/-- Actual algebraic simplicity implies a genuinely simple characteristic
zero at every complex source and energy, including any central energy. -/
theorem deriv_hillHminusDirichlet_ne_zero_of_multiplicity_one
    (q : PeriodOneHminusOne) (lambda : ℂ)
    (hm : singularDirichletAlgebraicMultiplicity (periodOneOriginal q) lambda = 1) :
    deriv (hillHminusDirichlet q) lambda ≠ 0 := by
  have hf := analyticOnNhd_hillHminusDirichlet_energy q lambda (mem_univ _)
  have ho : analyticOrderAt (hillHminusDirichlet q) lambda = 1 := by
    rw [← singularDirichletAlgebraicMultiplicity_eq_analyticOrderAt,hm]
    rfl
  have hd : analyticOrderAt (deriv (hillHminusDirichlet q)) lambda = 0 :=
    analyticOrderAt_deriv_of_pos hf (n := 0) (by simpa only [Nat.cast_zero,zero_add] using ho)
  intro hz
  exact (hf.deriv.analyticOrderAt_ne_zero.mpr hz) hd

/-- ONE cutoff works simultaneously for ALL high original complex labels on
ONE original H^-1 norm neighborhood: algebraic multiplicity one, nonzero
characteristic derivative, and actual analytic potential dependence. -/
theorem exists_uniform_simple_analytic_hillHminusDirichletComplexLabels
    (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      (∀ n : ℕ+, N < (n:ℕ) →
        AnalyticOnNhd ℂ (fun a => hillHminusDirichletComplexLabels a n) V) ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) →
        singularDirichletAlgebraicMultiplicity (periodOneOriginal a)
          (hillHminusDirichletComplexLabels a n) = 1 ∧
        deriv (hillHminusDirichlet a) (hillHminusDirichletComplexLabels a n) ≠ 0 := by
  let C := hillHminusMiuraChartAt q
  obtain ⟨N,V,hN,hV,hq,_,hc,han⟩ :=
    C.exists_uniform_analytic_dirichletControl q (mem_hillHminusMiuraChartAt q)
  refine ⟨N,V,hN,hV,hq,han,fun a ha n hn => ?_⟩
  have hm := hillHminusDirichletComplexLabels_multiplicity_one_of_control
    a (C.lift a) C.energyShift N (hc a ha) n hn
  exact ⟨hm,deriv_hillHminusDirichlet_ne_zero_of_multiplicity_one a _ hm⟩

/-- EVERY original complex native Dirichlet label, high or central, has an
actual zero-trace H1 eigenfunction with the source's literal L2 normalization. -/
theorem exists_normalized_hillHminusDirichletComplexLabel_eigenfunction
    (q : PeriodOneHminusOne) (n : ℕ+) :
    ∃ g : UnitDirichletH1,
      singularDirichletOperator (periodOneOriginal q) g =
        hillHminusDirichletComplexLabels q n • singularDirichletDomainInclusion g ∧
      ‖unitDirichletL2Inclusion g‖ = 1 ∧
      (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 :=
  exists_singularDirichlet_normalized_eigenfunction (periodOneOriginal q) _
    ((hillHminusDirichletComplexLabels_spectrum_iff q _).mpr ⟨n,rfl⟩)

end NLS.KdV
