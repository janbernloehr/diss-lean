import NLS.ZakharovShabat.SourceDirichletSpectralConservation
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Compact fixed-discriminant sheets for actual Dirichlet flows

The selected root and its terminal anti-discriminant stay on the compact
sheet above the initial periodic segment. The sheet is compact even
when the gap is collapsed. This bounds the actual scalar terminal data
throughout any real indexed integral-curve interval; global continuation
of the original source-space curve remains a separate requirement.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The compact algebraic sheet over one actual periodic segment,
using the original fixed source discriminant. -/
def sourceDirichletSpectralSheet
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p) : Set (ℂ × ℂ) :=
  {z | z.1 ∈ sourcePeriodicSegment hp hp1 φ n ∧
    z.2^2 = (canonicalDiscriminant hp (periodOnePotential φ) z.1)^2-4}

/-- The actual fixed spectral sheet is compact without an open-gap
assumption or a bound supplied by the caller. -/
theorem isCompact_sourceDirichletSpectralSheet
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p) :
    IsCompact (sourceDirichletSpectralSheet hp hp1 n φ) := by
  let K := sourcePeriodicSegment hp hp1 φ n
  let F : ℂ → ℂ := fun z => (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4
  have hK : IsCompact K := by
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hF : Continuous F :=
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ)).continuous.pow 2).sub continuous_const
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hclosed : IsClosed (sourceDirichletSpectralSheet hp hp1 n φ) :=
    (hK.isClosed.preimage continuous_fst).inter
      (isClosed_eq (continuous_snd.pow 2) (hF.comp continuous_fst))
  apply (hK.prod (isCompact_closedBall (0:ℂ) (max B 0+1))).of_isClosed_subset hclosed
  intro z hz
  refine ⟨hz.1,?_⟩
  have hnorm : ‖z.2‖^2 ≤ B := by
    rw [← norm_pow,hz.2]
    exact hB z.1 hz.1
  have hbound : ‖z.2‖ ≤ max B 0+1 := by
    have hb : B ≤ max B 0 := le_max_left _ _
    have hb0 : 0 ≤ max B 0 := le_max_right _ _
    nlinarith [norm_nonneg z.2]
  simpa only [mem_closedBall,dist_zero_right] using hbound

/-- The selected actual terminal is confined to the compact sheet of
any initial reference source throughout its real integral-curve interval. -/
theorem dirichletTerminal_mem_fixedSheet_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u t : ℝ) (hu : u ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ t) k,
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet k (γ t)) ∈
        sourceDirichletSpectralSheet hp hp1 k (γ u) := by
  have he := canonicalPeriodicEndpoints_eq_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p k k γ a b hreal hγ t u ht hu
  have hμ := canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1
    .dirichlet (γ t) (hreal t ht) k
  change canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ t) k ∈ segment ℝ _ _ at hμ
  rw [he.1,he.2] at hμ
  refine ⟨hμ,?_⟩
  have hD := canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p k γ a b hγ t u ht hu
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ t) k)
  change sourceAntiDiscriminantCandidate hp hp1 (γ t)
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ t) k)^2 = _
  rw [← sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot hp hp1 .dirichlet (γ t) k,hD]

/-- Every actual real indexed curve has one finite bound for both
selected terminal coordinates throughout its entire open time interval. -/
theorem exists_bound_dirichletTerminal_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u : ℝ) (hu : u ∈ Ioo a b) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Ioo a b,
      ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ t) k‖ ≤ R ∧
      ‖sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet k (γ t)‖ ≤ R := by
  obtain ⟨R,hR,hbound⟩ := (isCompact_sourceDirichletSpectralSheet hp hp1 k (γ u)).isBounded.exists_pos_norm_le
  refine ⟨R,hR,?_⟩
  intro t ht
  have he := hbound _ (dirichletTerminal_mem_fixedSheet_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p k γ a b hreal hγ u t hu ht)
  exact ⟨(norm_fst_le _).trans he,(norm_snd_le _).trans he⟩

end NLS.ZakharovShabat
