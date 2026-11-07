import NLS.SequenceSpaces.HilbertScalarGradient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A symmetric nonnegative matrix with bounded weighted column sums
has the corresponding unweighted quadratic bound. The weights may be
arbitrarily small or large; no equivalence of weighted norms is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace NLS

theorem weighted_two_mul_le (u v x y : ℝ) (hu : 0<u) (hv : 0<v) :
    2*x*y≤x^2*(v/u)+y^2*(u/v) := by
  have he : x^2*(v/u)+y^2*(u/v)-2*x*y=(x*v-y*u)^2/(u*v) := by
    field_simp [hu.ne',hv.ne']
    ring
  have h := div_nonneg (sq_nonneg (x*v-y*u)) (mul_pos hu hv).le
  rw [←he] at h
  linarith

theorem finite_symmetric_weighted_quadratic_bound
    {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (w x : ι → ℝ) (M : ℝ)
    (hA : ∀ i j, 0≤A i j) (hsym : ∀ i j, A i j=A j i)
    (hw : ∀ i, 0<w i) (hcol : ∀ j, (∑ i, A i j*w i)≤M*w j) :
    (∑ i, ∑ j, A i j*x i*x j)≤M*∑ i, (x i)^2 := by
  classical
  let T := ∑ j, ((x j)^2/w j)*(∑ i, A i j*w i)
  have hT : T≤M*∑ j, (x j)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      _≤((x j)^2/w j)*(M*w j) := mul_le_mul_of_nonneg_left (hcol j) (div_nonneg (sq_nonneg _) (hw j).le)
      _=M*(x j)^2 := by field_simp [(hw j).ne']
  have hleft : (∑ i, ∑ j, A i j*((x i)^2*(w j/w i)))=T := by
    dsimp only [T]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym i j]
    ring
  have hright : (∑ i, ∑ j, A i j*((x j)^2*(w i/w j)))=T := by
    rw [Finset.sum_comm]
    dsimp only [T]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum : 2*(∑ i, ∑ j, A i j*x i*x j)≤2*T := by
    calc
      _=∑ i, ∑ j, A i j*(2*x i*x j) := by simp_rw [Finset.mul_sum];ring
      _≤∑ i, ∑ j, A i j*((x i)^2*(w j/w i)+(x j)^2*(w i/w j)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (weighted_two_mul_le (w i) (w j) (x i) (x j) (hw i) (hw j)) (hA i j)
      _=(∑ i, ∑ j, A i j*((x i)^2*(w j/w i)))+
          (∑ i, ∑ j, A i j*((x j)^2*(w i/w j))) := by
        simp_rw [mul_add,Finset.sum_add_distrib]
      _=2*T := by rw [hleft,hright];ring
  linarith

theorem finite_symmetric_weighted_quadratic_bound_finset
    (s : Finset ℤ) (A : ℤ → ℤ → ℝ) (w x : ℤ → ℝ) (M : ℝ)
    (hA : ∀ i j, 0≤A i j) (hsym : ∀ i j, A i j=A j i)
    (hw : ∀ i, 0<w i) (hcol : ∀ j∈s, (∑ i∈s, A i j*w i)≤M*w j) :
    (∑ i∈s, ∑ j∈s, A i j*x i*x j)≤M*∑ i∈s, (x i)^2 := by
  classical
  have hc (j : s) : (∑ i : s, A i j*w i)≤M*w j := by
    rw [Finset.sum_coe_sort s (fun i : ℤ => A i j*w i)]
    exact hcol j j.property
  have h := finite_symmetric_weighted_quadratic_bound
    (fun i j : s => A i j) (fun i : s => w i) (fun i : s => x i) M
    (fun i j => hA i j) (fun i j => hsym i j) (fun i => hw i) hc
  have he : (∑ i : s, ∑ j : s, A i j*x i*x j)=∑ i∈s, ∑ j∈s, A i j*x i*x j := by
    calc
      _=∑ i∈s, ∑ j : s, A i j*x i*x j := Finset.sum_coe_sort s (fun i : ℤ => ∑ j : s, A i j*x i*x j)
      _=_ := Finset.sum_congr rfl (fun i _ => Finset.sum_coe_sort s (fun j : ℤ => A i j*x i*x j))
  rw [he,Finset.sum_coe_sort s (fun i : ℤ => (x i)^2)] at h
  exact h

end NLS
