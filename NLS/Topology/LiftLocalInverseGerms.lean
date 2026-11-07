import Mathlib.Topology.ContinuousOn

/-! Two-sided local inverse germs lift through continuous injective
inclusions when both recovered maps commute with those inclusions near
the chosen points. The stronger topology is retained in BOTH germs. -/
noncomputable section
open Filter Topology
namespace NLS.Topology

theorem lift_two_sided_inverse_germs
    {X Y A B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B]
    (f : X → Y) (g : Y → X) (F : A → B) (G : B → A) (S : A → X) (T : B → Y)
    (hS : Continuous S) (hT : Continuous T) (hiS : Function.Injective S) (hiT : Function.Injective T)
    (hF : ∀ a, T (F a)=f (S a)) (a : A) (hcF : ContinuousAt F a)
    (hG : ∀ᶠ b in 𝓝 (F a), S (G b)=g (T b))
    (hl : ∀ᶠ x in 𝓝 (S a), g (f x)=x) (hr : ∀ᶠ y in 𝓝 (f (S a)), f (g y)=y) :
    G (F a)=a ∧ (∀ᶠ x in 𝓝 a, G (F x)=x) ∧ (∀ᶠ y in 𝓝 (F a), F (G y)=y) := by
  have hTend : Tendsto T (𝓝 (F a)) (𝓝 (f (S a))) := by
    rw [← hF a]
    exact (hT.continuousAt (x:=F a)).tendsto
  have hpair : (∀ᶠ x in 𝓝 a, G (F x)=x) ∧ (∀ᶠ y in 𝓝 (F a), F (G y)=y) := by
    constructor
    · filter_upwards [hcF.eventually hG,(hS.continuousAt (x:=a)).eventually hl] with x hx hxl
      apply hiS
      rw [hx,hF,hxl]
    · filter_upwards [hG,hTend.eventually hr] with y hy hyr
      apply hiT
      rw [hF,hy,hyr]
  have hpoint : a ∈ {x | G (F x)=x} := mem_of_mem_nhds hpair.1
  exact ⟨hpoint,hpair⟩

end NLS.Topology
