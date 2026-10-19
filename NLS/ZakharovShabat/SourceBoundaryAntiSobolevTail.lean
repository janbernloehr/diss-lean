import NLS.ZakharovShabat.SourceBoundaryAntiFourierTail
import NLS.SequenceSpaces.DenseWeightedCoordinateBound
import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood

/-! # The boundary anti-discriminant tail for all Sobolev sources

Finite Fourier approximation extends the sharp tail to every original Hs source in a neighborhood, without smooth representatives.
-/

noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The literal anti-discriminant Fourier error at the canonically labelled
boundary root, on the original Sobolev source space. -/
def sourceBoundaryAntiFourierError (s : ℕ) (θ : BoundaryCondition) (n : ℤ)
    (ab : SobolevSource s) : ℂ :=
  sourceAntiDiscriminantCandidate (by norm_num) (by norm_num)
    (higherSobolevSourceInclusion s ab)
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
      (higherSobolevSourceInclusion s ab) n)+
    I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n-I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n)

/-- The actual boundary anti-discriminant Fourier error has a locally
uniform H^(s+1) tail for all original Hs sources near the real locus.
No smooth representative or additional source derivative is assumed. -/
theorem exists_local_sourceBoundaryAntiFourierError_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then sourceBoundaryAntiFourierError s θ n ab else 0) ∧
        ‖f‖ ≤ C := by
  classical
  obtain ⟨U₀,hU₀,haU₀,K,hK,C,hC,hbound⟩ :=
    exists_local_source_boundary_anti_fourier_tail_bound s hs a₀ θ
  let J := higherSobolevSourceInclusion s
  obtain ⟨V,hV,haV,hroots⟩ := exists_local_source_allBoundaryRoots_analytic
    (p := 2) (by norm_num) (by norm_num) (J a₀.val) a₀.property
  let U := U₀ ∩ J ⁻¹' V
  have hU : IsOpen U := hU₀.inter (hV.preimage J.continuous)
  let f (ab : SobolevSource s) (n : ℤ) :=
    if K ≤ n.natAbs then sourceBoundaryAntiFourierError s θ n ab else 0
  have hAc : Continuous (fun q : ℂ × NLS.CoeffPair 2 =>
      sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) q.2 q.1) :=
    continuousOn_univ.mp (analyticOnNhd_sourceAntiDiscriminantCandidate_joint (p := 2)
      (by norm_num) (by norm_num)).continuousOn
  have hf (n : ℤ) : ContinuousOn (fun ab => f ab n) U := by
    by_cases hn : K ≤ n.natAbs
    · simp only [f,if_pos hn]
      intro ab hab
      have hroot : ContinuousAt (fun x : SobolevSource s =>
          canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n) ab :=
        (hroots θ n (J ab) hab.2).continuousAt.comp J.continuous.continuousAt
      have ha : ContinuousAt (fun x : SobolevSource s =>
          sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) (J x)
            (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n)) ab :=
        ContinuousAt.comp
          (g := fun q : ℂ × NLS.CoeffPair 2 =>
            sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) q.2 q.1)
          (f := fun x : SobolevSource s =>
            (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n,J x))
          hAc.continuousAt (hroot.prodMk J.continuous.continuousAt)
      have hc₁ : Continuous (fun x : SobolevSource s => x.1.val (-n)) :=
        (WeightedCoeff.evalCLM _ 2 (-n)).continuous.comp continuous_fst
      have hc₂ : Continuous (fun x : SobolevSource s => x.2.val n) :=
        (WeightedCoeff.evalCLM _ 2 n).continuous.comp continuous_snd
      exact ((ha.add (continuousAt_const.mul hc₂.continuousAt)).sub
        (continuousAt_const.mul hc₁.continuousAt)).continuousWithinAt
    · simp only [f,if_neg hn]
      exact continuousOn_const
  refine ⟨U,hU,⟨haU₀,haV⟩,K,hK,C,hC,?_⟩
  intro ab hab
  apply WeightedCoeff.exists_of_dense_bounded_coordinates
    (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) (range (sobolevSourceOfFinsupp s)) U
    (denseRange_sobolevSourceOfFinsupp s) hU f hf C ?_ ab hab
  intro x hx hxfinite
  rcases hxfinite with ⟨c,rfl⟩
  obtain ⟨e,he,hen⟩ := hbound (sobolevSourceOfFinsupp s c) hx.1
    (polynomial c.1) (polynomial c.2) (contDiff_source_polynomial _) (contDiff_source_polynomial _)
    (periodic_source_polynomial _) (periodic_source_polynomial _)
    (by intro j; simp [sobolevSourceOfFinsupp]) (by intro j; simp [sobolevSourceOfFinsupp])
  exact ⟨e,he,hen⟩

end NLS.ZakharovShabat
