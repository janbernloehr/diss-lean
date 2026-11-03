import NLS.KdV.DirichletProjectionFreeComparison
import NLS.KdV.SingularDirichletRieszLinf
import NLS.KdV.HminusOneDirichletSourceCircles
import NLS.KdV.HminusOneDirichletComplexRealLabels
import NLS.FunctionalAnalysis.CompactThreshold

/-! Convergence of ACTUAL native Dirichlet source projections
to the ACTUAL free contour projection in physical L2-to-Linfinity norm.
The literal source circles and original positive indices are unchanged. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- Every original complex H^-1 source has a common neighborhood and cutoff
where ACTUAL Dirichlet projections approach the ACTUAL free contour operator
in the continuous-output uniform norm, ordinary L2-to-essential-supremum norm
and ordinary L2 operator norm, ALL at the SAME source circles and indices.
No circle, eigenfunction, mass lower bound or convergence estimate is supplied. -/
theorem exists_uniform_hillHminusDirichletProjection_sub_free_small
    (q : PeriodOneHminusOne) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) →
        ‖singularDirichletContinuousRieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖singularDirichletLinfRieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖singularDirichletL2RieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  let delta := min (1/16) (epsilon/80)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdsmall : delta ≤ 1/16 := min_le_left _ _
  have hde : delta ≤ epsilon/80 := min_le_right _ _
  obtain ⟨N₀,V₀,hN₀,hV₀,hq₀,hcompare⟩ :=
    exists_uniform_hillHminusDirichletEigenfunction_sine_comparison q hd
  obtain ⟨N₁,V₁,_,hV₁,hq₁,_,hcircles⟩ := exists_uniform_hillHminusDirichlet_sourceCircles q
  obtain ⟨N₂,V₂,_,_,hzero,_,hfree⟩ := exists_uniform_hillHminusDirichlet_sourceCircles 0
  let N := max N₀ (max N₁ N₂)
  refine ⟨N,V₀ ∩ V₁,hN₀.trans_le (le_max_left _ _),hV₀.inter hV₁,⟨hq₀,hq₁⟩,?_⟩
  intro a ha n hn
  have hn₀ : N₀ < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hn₁ : N₁ < (n:ℕ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hn₂ : N₂ < (n:ℕ) := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  obtain ⟨g,hg0,hg,he⟩ := hcompare a ha.1 n hn₀
  obtain ⟨hcq,hl,hiso,hmq⟩ := hcircles a ha.2 n hn₁
  obtain ⟨hc0,_,hiso0,hm0⟩ := hfree 0 hzero n hn₂
  simp only [map_zero,hillHminusDirichletComplexLabels_zero] at hc0 hiso0 hm0
  have hb := norm_singularDirichletProjection_sub_free_le_of_sine_error
    (periodOneOriginal a) n (hillHminusDirichletComplexLabels a n) hcq hc0 hl
    (fun z hz hs => (hiso z (ball_subset_closedBall hz)).mp hs)
    (fun z hz hs => (hiso0 z (ball_subset_closedBall hz)).mp hs)
    hmq hm0 g hg0 hg hd.le hdsmall he.le
  have hsmall : ‖singularDirichletContinuousRieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
      singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon :=
    hb.trans_lt (by linarith)
  exact ⟨hsmall,(norm_singularDirichletLinfRieszProjection_sub_le_uniform _ _ _ _).trans_lt hsmall,
    (norm_singularDirichletL2RieszProjection_sub_le_uniform _ _ _ _).trans_lt hsmall⟩

/-- On EVERY compact original H^-1 set, the actual source projections converge
UNIFORMLY to the actual free projection in all three physical operator norms.
Unlike a varying-tolerance neighborhood statement, the compact set is fixed
BEFORE epsilon. This supplies genuine uniform convergence on compact sets. -/
theorem exists_uniform_hillHminusDirichletProjection_cutoff_on_compact
    (K : Set PeriodOneHminusOne) (hK : IsCompact K) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧ ∀ a ∈ K, ∀ n : ℕ+, N < (n:ℕ) →
      ‖singularDirichletContinuousRieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
        singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
      ‖singularDirichletLinfRieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
        singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
      ‖singularDirichletL2RieszProjection (periodOneOriginal a) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
        singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let P : K → ℕ → Prop := fun a M => ∀ n : ℕ+, (n:ℕ) = M →
    ‖singularDirichletContinuousRieszProjection (periodOneOriginal a.val) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
      singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
    ‖singularDirichletLinfRieszProjection (periodOneOriginal a.val) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
      singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
    ‖singularDirichletL2RieszProjection (periodOneOriginal a.val) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
      singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon
  have hlocal (a : K) : ∃ N : ℕ, ∃ U : Set K, IsOpen U ∧ a ∈ U ∧
      ∀ b ∈ U, ∀ M : ℕ, N ≤ M → P b M := by
    obtain ⟨N,V,_,hV,ha,hb⟩ := exists_uniform_hillHminusDirichletProjection_sub_free_small a.val heps
    refine ⟨N+1,Subtype.val ⁻¹' V,hV.preimage continuous_subtype_val,ha,?_⟩
    intro b hbV M hM n hn
    exact hb b.val hbV n (by omega)
  obtain ⟨N,hN⟩ := NLS.exists_uniform_nat_threshold_on_compact P hlocal
  refine ⟨max N 1,by omega,?_⟩
  intro a ha n hn
  exact hN ⟨a,ha⟩ (n:ℕ) (by omega) n rfl

/-- The actual high eigenfunctions have the SOURCE unit physical L2 norm,
with one uniform sup-norm bound and one strictly positive COMPLEX bilinear
mass lower bound on an original complex H^-1 neighborhood and cutoff. -/
theorem exists_uniform_normalized_hillHminusDirichletEigenfunction_bounds
    (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1,
        singularDirichletOperator (periodOneOriginal a) g =
          hillHminusDirichletComplexLabels a n • singularDirichletDomainInclusion g ∧
        ‖unitDirichletL2Inclusion g‖ = 1 ∧
        (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
        ‖unitDirichletContinuousInclusion g‖ ≤ 4 ∧
        (1/16:ℝ) ≤ ‖singularDirichletDomainInclusion g g‖ := by
  obtain ⟨N,V,hN,hV,hq,hcompare⟩ :=
    exists_uniform_hillHminusDirichletEigenfunction_sine_comparison q (epsilon := 1/16) (by norm_num)
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn
  obtain ⟨f,_,hf,he⟩ := hcompare a ha n hn
  obtain ⟨g,hg,hnorm,hC,hM⟩ := exists_normalized_dirichletSineComparison_bounds
    (periodOneOriginal a) _ n f hf he.le
  refine ⟨g,hg,hnorm,?_,hC,hM⟩
  rw [← norm_sq_unitDirichletL2Inclusion,hnorm,one_pow]

end NLS.KdV
