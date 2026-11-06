import NLS.KdV.HillOriginalAllGapCartesianMatrix

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- Simultaneous physical analytic Cartesian germ families with the FULL
ORIGINAL four-entry Gardner matrix at EVERY mean-zero real L2 source.
All indices and low/closed selected gaps are included. Every germ and
physical matching condition is constructed; no canonical-map premise is
supplied. The neighborhoods may depend on the component. -/
theorem exists_hillOriginal_signedCartesian_hminus_Gardner_matrix_all_gaps
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0 = 0) :
    ∃ Z : Bool → ℕ+ → PeriodOneHminusOne → ℂ,
      (∀ (σ : Bool) (n : ℕ+),
        AnalyticAt ℂ (Z σ n) (hillOriginalHminusSource q.val) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          Z σ n (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p) ∧
      ∀ (σ τ : Bool) (n m : ℕ+),
        NLS.Poisson.hminusGardnerBracket (Z σ n) (Z τ m) (hillOriginalHminusSource q.val) =
          hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  let Z := fun (σ : Bool) (n : ℕ+) => hillOriginalSignedCartesianHminusGerm q n σ
  refine ⟨Z,(fun σ n => hillOriginalSignedCartesianHminusGerm_spec q n σ),?_⟩
  intro σ τ n m
  exact hillSignedCartesians_hminus_Gardner_original_matrix q hmean n m σ τ _ _
    (hillOriginalSignedCartesianHminusGerm_spec q n σ).1
    (hillOriginalSignedCartesianHminusGerm_spec q m τ).1
    (hillOriginalSignedCartesianHminusGerm_spec q n σ).2
    (hillOriginalSignedCartesianHminusGerm_spec q m τ).2

end NLS.KdV
