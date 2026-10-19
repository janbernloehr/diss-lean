import NLS.ZakharovShabat.SourceBoundaryAntiSobolevTail
import NLS.SequenceSpaces.WeightedTailCompletion
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! # The complete analytic anti-discriminant Fourier remainder

The literal error at canonical boundary roots is analytic into H^(s+1) on a common complex neighborhood of the real Hs locus.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual anti-discriminant Fourier error, realized in its sharper
Sobolev target whenever the source lies in the neighborhoods below. -/
def sourceBoundaryAntiFourierRemainder (s : ℕ) (θ : BoundaryCondition)
    (ab : SobolevSource s) : ScalarSobolev (s+1) :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev ((s+1:ℕ):ℝ)) 2
    (fun n => sourceBoundaryAntiFourierError s θ n ab)

/-- The complete literal anti-discriminant Fourier error is analytic into
H^(s+1) and locally bounded near every real Hs source, with no smoothness
hypothesis on the source and no deletion of central frequencies. -/
theorem exists_local_sourceBoundaryAntiFourierRemainder_analytic
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a₀.val ∈ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ AnalyticOnNhd ℂ (sourceBoundaryAntiFourierRemainder s θ) V ∧
        ∀ ab ∈ V, ‖sourceBoundaryAntiFourierRemainder s θ ab‖ ≤ C ∧
          ∀ n, (sourceBoundaryAntiFourierRemainder s θ ab).val n =
            sourceBoundaryAntiFourierError s θ n ab := by
  obtain ⟨U₀,hU₀,haU₀,K,_,C,hC,hbound⟩ :=
    exists_local_sourceBoundaryAntiFourierError_tail_bound s hs a₀ θ
  let J := higherSobolevSourceInclusion s
  obtain ⟨W,hW,haW,hroots⟩ := exists_local_source_allBoundaryRoots_analytic
    (p := 2) (by norm_num) (by norm_num) (J a₀.val) a₀.property
  let U := U₀ ∩ J ⁻¹' W
  have hU : IsOpen U := hU₀.inter (hW.preimage J.continuous)
  let f (ab : SobolevSource s) (n : ℤ) := sourceBoundaryAntiFourierError s θ n ab
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ab => f ab n) U := by
    intro ab hab
    have hroot : AnalyticAt ℂ (fun x : SobolevSource s =>
        canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n) ab :=
      (hroots θ n (J ab) hab.2).comp (J.analyticAt ab)
    have ha : AnalyticAt ℂ (fun x : SobolevSource s =>
        sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) (J x)
          (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n)) ab :=
      AnalyticAt.comp
        (g := fun q : ℂ × NLS.CoeffPair 2 =>
          sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) q.2 q.1)
        (f := fun x : SobolevSource s =>
          (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n,J x))
        (analyticOnNhd_sourceAntiDiscriminantCandidate_joint (p := 2)
          (by norm_num) (by norm_num) _ (mem_univ _))
        (hroot.prod (J.analyticAt ab))
    have hc₁ : AnalyticAt ℂ (fun x : SobolevSource s => x.1.val (-n)) ab :=
      ((WeightedCoeff.evalCLM _ 2 (-n)).analyticAt _).comp analyticAt_fst
    have hc₂ : AnalyticAt ℂ (fun x : SobolevSource s => x.2.val n) ab :=
      ((WeightedCoeff.evalCLM _ 2 n).analyticAt _).comp analyticAt_snd
    exact (ha.add (analyticAt_const.mul hc₂)).sub (analyticAt_const.mul hc₁)
  obtain ⟨V,hV,haV,hVU,B,hB,hfull⟩ := WeightedCoeff.exists_local_full_bound_of_tail
    (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) f hU
    (fun n => (hf n).continuousOn) K C hC (fun ab hab => hbound ab hab.1)
    a₀.val ⟨haU₀,haW⟩
  obtain ⟨han,hval⟩ := WeightedCoeff.analytic_realization_of_bound
    (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) f hV
    (fun n ab hab => hf n ab (hVU hab)) B hfull
  exact ⟨V,hV,haV,B,hB,han,hval⟩

/-- One open complex neighborhood of the real source locus supports both
complete, literal, one-order smoother anti-discriminant remainders. -/
theorem exists_sourceBoundaryAntiFourierRemainder_analytic_common_domain
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ (∀ a₀ : realTypeHigherSobolevSourceLocus s, a₀.val ∈ U) ∧
      ∀ θ : BoundaryCondition,
        AnalyticOnNhd ℂ (sourceBoundaryAntiFourierRemainder s θ) U ∧
        ∀ ab ∈ U, ∀ n, (sourceBoundaryAntiFourierRemainder s θ ab).val n =
          sourceBoundaryAntiFourierError s θ n ab := by
  let S : Set (SobolevSource s) := {ab | ∀ θ : BoundaryCondition,
    AnalyticAt ℂ (sourceBoundaryAntiFourierRemainder s θ) ab ∧
      ∀ n, (sourceBoundaryAntiFourierRemainder s θ ab).val n =
        sourceBoundaryAntiFourierError s θ n ab}
  refine ⟨interior S,isOpen_interior,?_,?_⟩
  · intro ab
    obtain ⟨Vd,hVd,had,Cd,_,hd,hcd⟩ :=
      exists_local_sourceBoundaryAntiFourierRemainder_analytic s hs ab .dirichlet
    obtain ⟨Vn,hVn,han,Cn,_,hn,hcn⟩ :=
      exists_local_sourceBoundaryAntiFourierRemainder_analytic s hs ab .neumann
    apply mem_interior_iff_mem_nhds.mpr
    apply mem_of_superset ((hVd.inter hVn).mem_nhds ⟨had,han⟩)
    intro x hx θ
    cases θ with
    | dirichlet => exact ⟨hd x hx.1,(hcd x hx.1).2⟩
    | neumann => exact ⟨hn x hx.2,(hcn x hx.2).2⟩
  · intro θ
    exact ⟨fun ab hab => (interior_subset hab θ).1,
      fun ab hab => (interior_subset hab θ).2⟩

@[simp] theorem sourceBoundaryAntiFourierRemainder_zero
    (s : ℕ) (θ : BoundaryCondition) : sourceBoundaryAntiFourierRemainder s θ 0 = 0 := by
  apply WeightedCoeff.ofFunctionOrZero_eq_of_coordinates
  intro n
  simp [sourceBoundaryAntiFourierError]

end NLS.ZakharovShabat
