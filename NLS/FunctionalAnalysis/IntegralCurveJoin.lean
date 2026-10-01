import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! # Joining actual integral curves at a common limit

Two curves with a common finite endpoint limit solve the same continuous
autonomous equation at their joining time as well. The value assigned
at the join is the common limit, independently of the original curves'
assigned endpoint values.
-/

noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*}

/-- Join two curves at their common limiting source value. -/
def joinIntegralCurve (c : ℝ) (ψ : E) (f g : ℝ → E) (t : ℝ) : E :=
  if t < c then f t else if c < t then g t else ψ

@[simp] theorem joinIntegralCurve_at (c : ℝ) (ψ : E) (f g : ℝ → E) :
    joinIntegralCurve c ψ f g c = ψ := by simp [joinIntegralCurve]

theorem joinIntegralCurve_of_lt (c : ℝ) (ψ : E) (f g : ℝ → E) {t : ℝ} (ht : t < c) :
    joinIntegralCurve c ψ f g t = f t := by simp [joinIntegralCurve,ht]

theorem joinIntegralCurve_of_gt (c : ℝ) (ψ : E) (f g : ℝ → E) {t : ℝ} (ht : c < t) :
    joinIntegralCurve c ψ f g t = g t := by simp [joinIntegralCurve,ht,ht.not_gt]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The joined curve solves the actual equation on the whole joined
interval, including at the join. Only continuity of the field at the
common limit is needed for this gluing step. -/
theorem hasDerivAt_joinIntegralCurve
    (V : E → E) (f g : ℝ → E) (ψ : E) (a c b : ℝ)
    (hac : a < c) (hcb : c < b)
    (hf : ∀ t ∈ Ioo a c, HasDerivAt f (V (f t)) t)
    (hg : ∀ t ∈ Ioo c b, HasDerivAt g (V (g t)) t)
    (hflim : Tendsto f (𝓝[Ioo a c] c) (𝓝 ψ))
    (hglim : Tendsto g (𝓝[Ioo c b] c) (𝓝 ψ))
    (hV : ContinuousAt V ψ) :
    ∀ t ∈ Ioo a b, HasDerivAt (joinIntegralCurve c ψ f g)
      (V (joinIntegralCurve c ψ f g t)) t := by
  let Γ := joinIntegralCurve c ψ f g
  have hΓc : Γ c = ψ := joinIntegralCurve_at c ψ f g
  have hleft (t : ℝ) (ht : t ∈ Ioo a c) : HasDerivAt Γ (V (Γ t)) t := by
    rw [show Γ t = f t from joinIntegralCurve_of_lt c ψ f g ht.2]
    apply (hf t ht).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    exact joinIntegralCurve_of_lt c ψ f g hs
  have hright (t : ℝ) (ht : t ∈ Ioo c b) : HasDerivAt Γ (V (Γ t)) t := by
    rw [show Γ t = g t from joinIntegralCurve_of_gt c ψ f g ht.1]
    apply (hg t ht).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht.1] with s hs
    exact joinIntegralCurve_of_gt c ψ f g hs
  have hleftlim : Tendsto Γ (𝓝[Ioo a c] c) (𝓝 ψ) := by
    apply hflim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (joinIntegralCurve_of_lt c ψ f g ht.2).symm
  have hrightlim : Tendsto Γ (𝓝[Ioo c b] c) (𝓝 ψ) := by
    apply hglim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (joinIntegralCurve_of_gt c ψ f g ht.1).symm
  have hleftder : HasDerivWithinAt Γ (V ψ) (Iic c) c := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hleft t ht).differentiableAt.differentiableWithinAt)
      (by simpa only [ContinuousWithinAt,hΓc] using hleftlim) (Ioo_mem_nhdsLT hac)
    have hlim : Tendsto Γ (𝓝[<] c) (𝓝 ψ) := by
      simpa only [nhdsWithin_Ioo_eq_nhdsLT hac] using hleftlim
    apply (hV.tendsto.comp hlim).congr'
    filter_upwards [Ioo_mem_nhdsLT hac] with t ht
    exact (hleft t ht).deriv.symm
  have hrightder : HasDerivWithinAt Γ (V ψ) (Ici c) c := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hright t ht).differentiableAt.differentiableWithinAt)
      (by simpa only [ContinuousWithinAt,hΓc] using hrightlim) (Ioo_mem_nhdsGT hcb)
    have hlim : Tendsto Γ (𝓝[>] c) (𝓝 ψ) := by
      simpa only [nhdsWithin_Ioo_eq_nhdsGT hcb] using hrightlim
    apply (hV.tendsto.comp hlim).congr'
    filter_upwards [Ioo_mem_nhdsGT hcb] with t ht
    exact (hright t ht).deriv.symm
  intro t ht
  change HasDerivAt Γ (V (Γ t)) t
  rcases lt_trichotomy t c with htc | rfl | hct
  · exact hleft t ⟨ht.1,htc⟩
  · rw [hΓc]
    simpa using hleftder.union hrightder
  · exact hright t ⟨hct,ht.2⟩

end NLS.FunctionalAnalysis
