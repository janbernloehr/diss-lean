import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Contractible neighborhoods from a nonexpansive projection

A contractible real domain has a contractible open thickening inside any prescribed open ambient neighborhood.
-/

noncomputable section
open Set Metric ContinuousMap
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Straight segments to a contractible subdomain contract the ambient domain. -/
theorem contractible_of_segments_to_subdomain
    (U A : Set E) (hAU : A ⊆ U) [ContractibleSpace A]
    (P : E → E) (hP : Continuous P) (hPA : ∀ x ∈ U, P x ∈ A)
    (hsegment : ∀ x ∈ U, segment ℝ x (P x) ⊆ U) :
    ContractibleSpace U := by
  let Q : C(U,A) := {
    toFun := fun x => ⟨P x.val,hPA x.val x.property⟩
    continuous_toFun := (hP.comp continuous_subtype_val).subtype_mk _
  }
  let i : C(A,U) := {
    toFun := fun x => ⟨x.val,hAU x.property⟩
    continuous_toFun := continuous_subtype_val.subtype_mk _
  }
  let R : C(U,U) := i.comp Q
  obtain ⟨z,⟨H₀⟩⟩ := (contractible_iff_id_nullhomotopic A).mp (inferInstance : ContractibleSpace A)
  let H : (ContinuousMap.id U).Homotopy R := {
    toFun := fun q => ⟨(1-(q.1:ℝ)) • q.2.val+(q.1:ℝ) • P q.2.val,by
      apply hsegment q.2.val q.2.property
      exact ⟨1-(q.1:ℝ),(q.1:ℝ),sub_nonneg.mpr q.1.property.2,q.1.property.1,
        sub_add_cancel _ _,rfl⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (hP.comp (continuous_subtype_val.comp continuous_snd)))
    map_zero_left := by intro x; apply Subtype.ext; simp
    map_one_left := by intro x; apply Subtype.ext; simp [R,i,Q]
  }
  let G : R.Homotopy (ContinuousMap.const U (i z)) := {
    toFun := fun q => i (H₀ (q.1,Q q.2))
    continuous_toFun := i.continuous.comp (H₀.continuous.comp
      (continuous_fst.prodMk (Q.continuous.comp continuous_snd)))
    map_zero_left := by intro x; simp [R]
    map_one_left := by intro x; simp
  }
  exact (contractible_iff_id_nullhomotopic U).mpr ⟨i z,⟨H.trans G⟩⟩

/-- A nonexpansive projection thickens a relatively open contractible
real domain inside any prescribed open ambient neighborhood. -/
theorem exists_contractible_open_neighborhood_of_projection
    (A G : Set E) [ContractibleSpace A]
    (P : E → E) (hP : LipschitzWith 1 P)
    (hfix : ∀ a ∈ A, P a = a)
    (hpre : IsOpen (P ⁻¹' A)) (hG : IsOpen G) (hAG : A ⊆ G) :
    ∃ U : Set E, IsOpen U ∧ A ⊆ U ∧ U ⊆ G ∧ ContractibleSpace U := by
  classical
  have hlocal (a : A) : ∃ r : ℝ, 0 < r ∧ ball a.val r ⊆ G ∩ P ⁻¹' A := by
    apply Metric.isOpen_iff.mp (hG.inter hpre)
    exact ⟨hAG a.property,by simpa only [mem_preimage,hfix a.val a.property] using a.property⟩
  choose r hr hb using hlocal
  let U : Set E := ⋃ a : A, ball a.val (r a)
  have hAU : A ⊆ U := fun a ha => mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hr ⟨a,ha⟩)⟩
  have hUG : U ⊆ G := by
    intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    exact (hb a ha).1
  refine ⟨U,isOpen_iUnion (fun _ => isOpen_ball),hAU,hUG,?_⟩
  apply contractible_of_segments_to_subdomain U A hAU P hP.continuous
  · intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    exact (hb a ha).2
  · intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    have hpball : P x ∈ ball a.val (r a) := by
      rw [mem_ball]
      calc
        dist (P x) a.val = dist (P x) (P a.val) := by rw [hfix a.val a.property]
        _ ≤ dist x a.val := by simpa only [NNReal.coe_one,one_mul] using hP.dist_le_mul x a.val
        _ < r a := mem_ball.mp ha
    intro y hy
    exact mem_iUnion.mpr ⟨a,(convex_ball a.val (r a)).segment_subset ha hpball hy⟩

end NLS.FunctionalAnalysis

namespace NLS.FunctionalAnalysis
open Set
variable {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transfer a contractible real domain through an isometric inclusion
and thicken it inside a prescribed complex open neighborhood. -/
theorem exists_contractible_open_neighborhood_of_isometric_retract
    (i : E → F) (hi : Isometry i) (R : F → E) (hR : Continuous R)
    (hleft : ∀ x, R (i x) = x) (hP : LipschitzWith 1 (i ∘ R))
    (A : Set E) (hA : IsOpen A) [ContractibleSpace A]
    (G : Set F) (hG : IsOpen G) (hAG : i '' A ⊆ G) :
    ∃ U : Set F, IsOpen U ∧ i '' A ⊆ U ∧ U ⊆ G ∧ ContractibleSpace U := by
  let : ContractibleSpace (i '' A) := (hi.isEmbedding.homeomorphImage A).symm.contractibleSpace
  have hpre : (i ∘ R) ⁻¹' (i '' A) = R ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨a,ha,he⟩
      have hae : a = R x := hi.injective he
      change R x ∈ A
      rwa [← hae]
    · intro hx
      exact ⟨R x,hx,rfl⟩
  apply exists_contractible_open_neighborhood_of_projection (i '' A) G (i ∘ R) hP
  · rintro _ ⟨a,ha,rfl⟩
    simp only [Function.comp_apply,hleft]
  · rw [hpre]
    exact hA.preimage hR
  · exact hG
  · exact hAG

end NLS.FunctionalAnalysis
