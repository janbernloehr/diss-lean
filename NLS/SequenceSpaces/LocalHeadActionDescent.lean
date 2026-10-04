import NLS.SequenceSpaces.HeadActionPathNeighborhood
import NLS.SequenceSpaces.HeadActionCurveInvariance
import Mathlib.Analysis.Complex.RealDeriv

/-! # Local analytic factorization through all quadratic actions

The explicit paths connect every point in a common neighborhood to the
analytic section while preserving its actions. Rotation stationarity
therefore gives exact recovery through the full action map.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Neighborhoods supporting exact analytic descent through the head actions. -/
structure HeadActionChart (S : Finset ℤ) (U : Set (TailSumSpace q S)) (a : TailSumSpace q S) where
  source : Set (TailSumSpace q S)
  target : Set (Coeff q)
  head_nonzero : HeadNonzero S a
  source_open : IsOpen source
  target_open : IsOpen target
  base_mem : a ∈ source
  source_subset : source ⊆ U
  map_mem : ∀ w ∈ source, headActions S w ∈ target
  section_mem : ∀ b ∈ target, headActionSection S a b ∈ source
  section_analytic : AnalyticOnNhd ℂ (headActionSection S a) target
  path_zero : ∀ w ∈ source, headActionPath S a (w,0) = w
  path_good : ∀ w ∈ source, ∀ t ∈ Icc (0 : ℝ) 1,
    AnalyticAt ℂ (headActionPath S a) (w,(t : ℂ)) ∧
      headActionPath S a (w,(t : ℂ)) ∈ U ∧ HeadNonzero S (headActionPath S a (w,(t : ℂ)))

/-- Every nonzero retained head admits a local action chart. -/
theorem exists_headActionChart (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a)
    (U : Set (TailSumSpace q S)) (hU : IsOpen U) (haU : a ∈ U) : Nonempty (HeadActionChart S U a) := by
  obtain ⟨V,hV,haV,hVU,hpath⟩ := exists_headActionPath_neighborhood S a ha U hU haU
  obtain ⟨T,hT,haT,hsec,hinto⟩ := exists_headActionSection_neighborhood S a ha V hV haV
  have hA : Continuous (headActions (q := q) S) := continuousOn_univ.mp (analyticOnNhd_headActions S).continuousOn
  refine ⟨⟨V ∩ headActions S ⁻¹' T,T,ha,hV.inter (hT.preimage hA),hT,⟨haV,haT⟩,
    fun _ hw => hVU hw.1,fun _ hw => hw.2,?_,hsec,fun w hw => (hpath w hw.1).1,
    fun w hw => (hpath w hw.1).2⟩⟩
  intro b hb
  refine ⟨hinto hb,?_⟩
  change headActions S (headActionSection S a b) ∈ T
  simpa only [headActions_section S a ha] using hb

namespace HeadActionChart
variable {S : Finset ℤ} {U : Set (TailSumSpace q S)} {a : TailSumSpace q S}

@[simp] theorem image_source (C : HeadActionChart S U a) : headActions S '' C.source = C.target := by
  apply Subset.antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact C.map_mem w hw
  · intro b hb
    exact ⟨headActionSection S a b,C.section_mem b hb,headActions_section S a C.head_nonzero b⟩

theorem target_base_mem (C : HeadActionChart S U a) : headActions S a ∈ C.target := C.map_mem a C.base_mem

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The local factor evaluates the original function on the action section. -/
def factor (_C : HeadActionChart S U a) (G : TailSumSpace q S → F) : Coeff q → F :=
  G ∘ headActionSection S a

theorem analyticOnNhd_factor (C : HeadActionChart S U a) (G : TailSumSpace q S → F)
    (hG : AnalyticOnNhd ℂ G U) : AnalyticOnNhd ℂ (C.factor G) C.target :=
  hG.comp C.section_analytic (fun b hb => C.source_subset (C.section_mem b hb))

/-- Rotation stationarity now yields exact recovery throughout the source
neighborhood; no joining-curve hypothesis is left to the caller. -/
theorem factor_apply (C : HeadActionChart S U a) (hU : IsOpen U)
    (G : TailSumSpace q S → F) (hG : DifferentiableOn ℂ G U)
    (hrot : ∀ w ∈ U, ∀ k : S, fderiv ℂ G w (headRotationVector S k w) = 0)
    (w : TailSumSpace q S) (hw : w ∈ C.source) : C.factor G (headActions S w) = G w := by
  let γ : ℝ → TailSumSpace q S := fun t => headActionPath S a (w,(t : ℂ))
  let dγ : ℝ → TailSumSpace q S := fun t => deriv (fun z : ℂ => headActionPath S a (w,z)) (t : ℂ)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt γ (dγ t) t := by
    have hc : AnalyticAt ℂ (fun z : ℂ => (w,z)) (t : ℂ) := analyticAt_const.prod analyticAt_id
    have hh := ((C.path_good w hw t ht).1.comp hc).differentiableAt.hasDerivAt
    have hr := (hh.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (Complex.ofRealCLM.hasDerivAt (x := t))
    change HasDerivAt γ ((1 : ℂ) • dγ t) t at hr
    simpa only [one_smul] using hr
  have he := eq_of_headAction_curve S G U hU hG hrot γ dγ hd
    (fun t ht => (C.path_good w hw t ht).2.1)
    (fun t ht => (C.path_good w hw t ht).2.2)
    (fun t => by dsimp only [γ]; rw [headActions_path S a C.head_nonzero,headActions_path S a C.head_nonzero])
  change G (headActionSection S a (headActions S w)) = G w
  simpa only [γ,Complex.ofReal_one,Complex.ofReal_zero,headActionPath_one,C.path_zero w hw] using he

omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- A factor satisfying recovery is unique on the chosen action neighborhood. -/
theorem factor_unique (C : HeadActionChart S U a) (G : TailSumSpace q S → F) (H : Coeff q → F)
    (hH : ∀ w ∈ C.source, H (headActions S w) = G w) : EqOn H (C.factor G) C.target := by
  intro b hb
  change H b = G (headActionSection S a b)
  simpa only [headActions_section S a C.head_nonzero] using hH _ (C.section_mem b hb)

end HeadActionChart
end NLS.Coeff
