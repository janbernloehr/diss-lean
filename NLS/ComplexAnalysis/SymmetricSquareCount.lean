import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite multiplicity counts under a complex shifted squaring map.
Nonzero fibers consist of a reflected pair, while the ramified fiber at
the shifted zero has one point and its prescribed odd multiplicity. -/
noncomputable section
open scoped BigOperators
namespace NLS.ComplexAnalysis

/-- A finite symmetric set has exactly the expected two-point square fiber. -/
theorem filter_square_sub_eq_pair (K : Finset ℂ) (c z : ℂ)
    (hz : z ∈ K) (hneg : ∀ w ∈ K, -w ∈ K) :
    K.filter (fun w => w^2-c = z^2-c) = {z,-z} := by
  classical
  ext w
  simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,
    sub_left_inj,sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · exact fun h => h.2
  · rintro (rfl | rfl)
    · exact ⟨hz,Or.inl rfl⟩
    · exact ⟨hneg z hz,Or.inr rfl⟩

/-- The ramified fiber has exactly one point, independently of its multiplicity. -/
theorem filter_square_sub_eq_neg (K : Finset ℂ) (c : ℂ) (h0 : 0 ∈ K) :
    K.filter (fun w => w^2-c = -c) = {0} := by
  classical
  have he (w : ℂ) : w^2-c = -c ↔ w = 0 := by
    constructor
    · intro h
      apply sq_eq_zero_iff.mp
      linear_combination h
    · rintro rfl
      simp
  ext w
  simp only [Finset.mem_filter,he,Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl
    exact ⟨h0,rfl⟩

/-- Removing the auxiliary odd factor and quotienting a symmetric finite
frequency set by squaring gives the EXACT scalar multiplicity count.
The scalar shifted-zero energy is retained even when its multiplicity is zero. -/
theorem sum_symmetric_square_multiplicity (K : Finset ℂ) (c : ℂ)
    (a m : ℂ → ℕ) (h0 : 0 ∈ K) (hneg : ∀ z ∈ K, -z ∈ K)
    (ha0 : a 0 = 1+2*m (-c))
    (ha : ∀ z ∈ K, z ≠ 0 → a z = m (z^2-c)) :
    (∑ z ∈ K, a z) = 1+2*∑ e ∈ K.image (fun z => z^2-c), m e := by
  classical
  let S := K.image (fun z => z^2-c)
  have hS0 : -c ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨0,h0,by simp⟩
  have hfiber (e : ℂ) (he : e ∈ S) :
      (∑ z ∈ K.filter (fun z => z^2-c = e), a z) =
        (if e = -c then 1 else 0)+2*m e := by
    by_cases he0 : e = -c
    · subst e
      rw [filter_square_sub_eq_neg K c h0]
      simp [ha0]
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
      have hz0 : z ≠ 0 := by
        intro h
        apply he0
        simp [h]
      have hzn : z ≠ -z := by
        intro h
        apply hz0
        linear_combination (1/2:ℂ)*h
      rw [filter_square_sub_eq_pair K c z hz hneg,
        Finset.sum_pair hzn,ha z hz hz0,ha (-z) (hneg z hz) (neg_ne_zero.mpr hz0)]
      simp only [neg_sq,if_neg he0,zero_add]
      omega
  rw [← Finset.sum_fiberwise_of_maps_to (t := S)
    (fun z hz => Finset.mem_image_of_mem (fun w : ℂ => w^2-c) hz) a]
  calc
    _ = ∑ e ∈ S, ((if e = -c then 1 else 0)+2*m e) :=
      Finset.sum_congr rfl hfiber
    _ = 1+2*∑ e ∈ S, m e := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_ite_eq',hS0,if_pos]

end NLS.ComplexAnalysis
