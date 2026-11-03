import NLS.Articles.KdVPseudomeasures.OriginalComplexDirichletLabels
import NLS.KdV.HminusOneDirichletUniformSimplicity

/-! The Section 2.5 Dirichlet prerequisites on the ENTIRE ORIGINAL complex
H^-1 distribution domain. A common original norm neighborhood supports all
simple analytic high labels; native eigenfunctions have the exact [0,1] L2 norm. -/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual native original eigenfunction is normalized in the literal
unnormalized unit-interval L2 norm, with both Dirichlet traces retained. -/
theorem exists_normalized_originalComplexDirichlet_eigenfunction
    (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    ∃ g : UnitDirichletH1,
      singularDirichletOperator q.val g =
        originalComplexDirichletLabels q n • singularDirichletDomainInclusion g ∧
      ‖unitDirichletL2Inclusion g‖ = 1 ∧
      (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 := by
  have h := exists_normalized_hillHminusDirichletComplexLabel_eigenfunction
    (periodOneOriginalExtract q.val) n
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- ONE original H^-1 norm neighborhood and cutoff make ALL high original
Dirichlet labels algebraically simple, with nonzero characteristic derivative.
The labels have actual analytic extensions to that SAME open original norm
neighborhood. Outside the physical period-one locus only the extension is
used; all native operator assertions retain the original physical locus. -/
theorem exists_uniform_originalComplexDirichlet_simple_analytic
    (q : OriginalComplexHminusOnePotential) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      (∀ n : ℕ+, N < (n:ℕ) → AnalyticOnNhd ℂ
        (fun a => hillHminusDirichletComplexLabels (periodOneOriginalExtract a) n) U) ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) →
          singularDirichletAlgebraicMultiplicity a.val (originalComplexDirichletLabels a n) = 1 ∧
          deriv (originalComplexDirichletCharacteristic a) (originalComplexDirichletLabels a n) ≠ 0 := by
  let F := periodOneOriginalExtract
  obtain ⟨N,V,hN,hV,hqV,han,hsimple⟩ :=
    exists_uniform_simple_analytic_hillHminusDirichletComplexLabels (F q.val)
  refine ⟨N,F ⁻¹' V,hN,hV.preimage F.continuous,hqV,?_,?_⟩
  · intro n hn a ha
    exact (han n hn (F a) ha).comp (f := F) (F.analyticAt a)
  · intro a ha n hn
    have h := hsimple (F a.val) ha n hn
    change singularDirichletAlgebraicMultiplicity
      (periodOneOriginal (periodOneOriginalExtract a.val)) (originalComplexDirichletLabels a n) = 1 ∧
      deriv (originalComplexDirichletCharacteristic a) (originalComplexDirichletLabels a n) ≠ 0 at h
    rw [originalComplexDirichlet_distribution a] at h
    exact h

end NLS.Articles.KdVPseudomeasures
