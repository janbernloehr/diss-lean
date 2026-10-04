import NLS.SequenceSpaces.TailSumCoordinates

/-! # Local analytic descent to tail sums

An explicit affine section supplies a local factor through the tail sums.
The domain is chosen so that each point and its section representative
are joined inside a ball in the original domain. The neighborhoods depend
only on that domain and the base point, not on the function or target norm.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Common neighborhoods for analytic descent along tail redistributions. -/
structure TailSumChart (S : Finset ℤ) (U : Set (Coeff q × Coeff q))
    (a : Coeff q × Coeff q) where
  source : Set (Coeff q × Coeff q)
  target : Set (TailSumSpace q S)
  source_open : IsOpen source
  target_open : IsOpen target
  base_mem : a ∈ source
  source_subset : source ⊆ U
  map_mem : ∀ b ∈ source, tailSumCLM S b ∈ target
  section_mem : ∀ w ∈ target, tailSumSection S a w ∈ source
  segment_subset : ∀ b ∈ source, segment ℝ b (tailSumSection S a (tailSumCLM S b)) ⊆ U

/-- Tail-sum charts exist at every point of every open mixed-coordinate domain. -/
theorem exists_tailSumChart (S : Finset ℤ) (U : Set (Coeff q × Coeff q))
    (hU : IsOpen U) (a : Coeff q × Coeff q) (ha : a ∈ U) :
    Nonempty (TailSumChart S U a) := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hU a ha
  let T := tailSumSection S a ⁻¹' ball a R
  let V := ball a R ∩ tailSumCLM S ⁻¹' T
  have hT : IsOpen T := isOpen_ball.preimage (continuous_iff_continuousAt.mpr fun w => (analyticAt_tailSumSection S a w).continuousAt)
  have hV : IsOpen V := isOpen_ball.inter (hT.preimage (tailSumCLM S).continuous)
  have haT : tailSumCLM S a ∈ T := by
    change tailSumSection S a (tailSumCLM S a) ∈ ball a R
    rw [tailSumSection_base]
    exact mem_ball_self hR
  refine ⟨⟨V,T,hV,hT,⟨mem_ball_self hR,haT⟩,fun _ hb => hball hb.1,
    fun _ hb => hb.2,?_,?_⟩⟩
  · intro w hw
    refine ⟨hw,?_⟩
    change tailSumCLM S (tailSumSection S a w) ∈ T
    simpa using hw
  · intro b hb
    exact ((convex_ball a R).segment_subset hb.1 hb.2).trans hball

namespace TailSumChart
variable {S : Finset ℤ} {U : Set (Coeff q × Coeff q)} {a : Coeff q × Coeff q}

@[simp] theorem image_source (C : TailSumChart S U a) : tailSumCLM S '' C.source = C.target := by
  apply Set.Subset.antisymm
  · rintro _ ⟨b,hb,rfl⟩
    exact C.map_mem b hb
  · intro w hw
    exact ⟨tailSumSection S a w,C.section_mem w hw,tailSum_section S a w⟩

theorem target_base_mem (C : TailSumChart S U a) : tailSumCLM S a ∈ C.target :=
  C.map_mem a C.base_mem

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The explicit local factor is obtained by evaluation on the affine section. -/
def factor (_C : TailSumChart S U a) (G : (Coeff q × Coeff q) → F) : TailSumSpace q S → F :=
  fun w => G (tailSumSection S a w)

theorem analyticOnNhd_factor (C : TailSumChart S U a) (G : (Coeff q × Coeff q) → F)
    (hG : AnalyticOnNhd ℂ G U) : AnalyticOnNhd ℂ (C.factor G) C.target := by
  intro w hw
  exact (hG _ (C.source_subset (C.section_mem w hw))).comp (analyticAt_tailSumSection S a w)

/-- Tail stationarity yields exact local recovery, including at zero entries. -/
theorem factor_apply (C : TailSumChart S U a) (hq : q ≠ ⊤) (hU : IsOpen U)
    (G : (Coeff q × Coeff q) → F) (hG : DifferentiableOn ℂ G U)
    (hD : ∀ b ∈ U, ∀ k ∉ S, fderiv ℂ G b (actionSplitDirection q k) = 0)
    (b : Coeff q × Coeff q) (hb : b ∈ C.source) : C.factor G (tailSumCLM S b) = G b := by
  have he : tailSumCLM S b = tailSumCLM S (tailSumSection S a (tailSumCLM S b)) := by simp
  obtain ⟨hh,hs⟩ := (tailSumCLM_eq_iff S _ _).mp he
  exact eq_of_same_tailActions_of_segment hq G U hU hG S hD b _ hh hs (C.segment_subset b hb)

omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- Every local factor satisfying recovery agrees with the explicit section factor. -/
theorem factor_unique (C : TailSumChart S U a) (G : (Coeff q × Coeff q) → F)
    (H : TailSumSpace q S → F) (hH : ∀ b ∈ C.source, H (tailSumCLM S b) = G b) :
    EqOn H (C.factor G) C.target := by
  intro w hw
  simpa [factor] using hH _ (C.section_mem w hw)

end TailSumChart
end NLS.Coeff
