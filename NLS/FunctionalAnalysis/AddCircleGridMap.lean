import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Scaled quotient maps for periodic integer-grid covers

The real grid is mapped into the product of unit additive circles by
coordinatewise division by a positive integer. Fibers differ by integer
multiples of that mesh denominator. The quotient map is open and contracts
each coordinate distance by at least that denominator.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis
universe u
variable {ι : Type u}

/-- The coordinatewise scaled quotient into the unit additive circle. -/
def addCircleGridMap (M : ℕ) (x : ι → ℝ) : ι → AddCircle (1 : ℝ) :=
  fun i => ((x i / M : ℝ) : AddCircle (1 : ℝ))

theorem addCircleGridMap_surjective {M : ℕ} (hM : 0 < M) :
    Function.Surjective (addCircleGridMap (ι := ι) M) := by
  intro z
  have hz (i) : ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = z i :=
    QuotientAddGroup.mk_surjective (z i)
  choose x hx using hz
  refine ⟨fun i => x i * M, ?_⟩
  funext i
  simp only [addCircleGridMap, mul_div_cancel_right₀ _ (show (M : ℝ) ≠ 0 by positivity)]
  exact hx i

/-- Two lifts differ by integer multiples of the mesh denominator. -/
theorem addCircleGridMap_eq_iff {M : ℕ} (hM : 0 < M) (x y : ι → ℝ) :
    addCircleGridMap M x = addCircleGridMap M y ↔
      ∃ k : ι → ℤ, ∀ i, x i = y i + M * k i := by
  have hMR : (M : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    have hi (i) : ∃ k : ℤ, x i = y i + M * k := by
      have he : ((x i / M - y i / M : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]
        exact congrFun h i
      obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp he
      refine ⟨k,?_⟩
      simp only [zsmul_eq_mul,mul_one] at hk
      rw [← sub_div, eq_div_iff hMR] at hk
      linarith
    exact Classical.axiomOfChoice hi
  · rintro ⟨k,hk⟩
    funext i
    apply sub_eq_zero.mp
    change ((x i / M : ℝ) : AddCircle (1 : ℝ)) - ((y i / M : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [← AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    refine ⟨k i,?_⟩
    simp only [zsmul_eq_mul,mul_one]
    rw [← sub_div,eq_div_iff hMR,hk i]
    ring

/-- The scaled quotient is open, including for an arbitrary product of circles. -/
theorem isOpenMap_addCircleGridMap {M : ℕ} (hM : 0 < M) :
    IsOpenMap (addCircleGridMap (ι := ι) M) := by
  have hMR : (M : ℝ) ≠ 0 := by positivity
  have hopen : IsOpenMap (fun x : ℝ => ((x / M : ℝ) : AddCircle (1 : ℝ))) := by
    simpa only [Function.comp_def,Homeomorph.mulRight₀_symm_apply,div_eq_mul_inv] using
      (QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))).comp
        (Homeomorph.mulRight₀ (M : ℝ) hMR).symm.isOpenMap
  have hsurj : Function.Surjective (fun x : ℝ => ((x / M : ℝ) : AddCircle (1 : ℝ))) := by
    intro z
    obtain ⟨x,hx⟩ := QuotientAddGroup.mk_surjective z
    exact ⟨x*M,by simpa only [mul_div_cancel_right₀ _ hMR] using hx⟩
  exact IsOpenMap.piMap (fun _ : ι => hopen) (Filter.Eventually.of_forall (fun _ => hsurj))

/-- Quotient distance is bounded by the scaled real-coordinate distance. -/
theorem addCircleGridMap_dist_le {M : ℕ} (hM : 0 < M) (x y : ι → ℝ) (i : ι) :
    dist (addCircleGridMap M x i) (addCircleGridMap M y i) ≤ |x i - y i| / M := by
  rw [dist_eq_norm]
  change ‖((x i / M : ℝ) : AddCircle (1 : ℝ)) - (y i / M : ℝ)‖ ≤ _
  rw [← AddCircle.coe_sub]
  calc
    _ ≤ ‖x i / M - y i / M‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |x i - y i| / M := by rw [← sub_div,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : (0 : ℝ) < M)]

end NLS.FunctionalAnalysis
