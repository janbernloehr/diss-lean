import NLS.SequenceSpaces.SubcriticalTwoScaleSum
import NLS.SequenceSpaces.HillLogKernel

/-! Reduction of the full quadratic reciprocal lattice to a positive
two-scale series. Both resonances are explicitly omitted. -/
noncomputable section
open Set
namespace NLS.ReciprocalSeries

def quadraticPowerKernel (s : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  if k=(n:ℤ) ∨ k=-(n:ℤ) then 0 else |(n:ℝ)+(k:ℝ)|^(-s)*|(n:ℝ)-(k:ℝ)|^(-s)

def twoScalePower (s : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  if k=0 then 0 else |(k:ℝ)|^(-s)*((n:ℝ)+|(k:ℝ)|)^(-s)

theorem twoScalePower_positive (s : ℝ) (n j : ℕ) :
    twoScalePower s n ((j:ℤ)+1)=((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s) := by
  simp only [twoScalePower,if_neg (by omega : (j:ℤ)+1≠0),Int.cast_add,Int.cast_natCast,
    Int.cast_one,abs_of_pos (by positivity : 0<(j:ℝ)+1),add_assoc]

theorem twoScalePower_neg (s : ℝ) (n : ℕ) (k : ℤ) :
    twoScalePower s n (-k)=twoScalePower s n k := by
  simp only [twoScalePower,neg_eq_zero,Int.cast_neg,abs_neg]

theorem summable_twoScalePower (s : ℝ) (hs : (1:ℝ)/2 < s) (n : ℕ) :
    Summable (twoScalePower s n) := by
  have hp : Summable (fun j : ℕ => ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)) := by
    apply (summable_nat_shifted_rpow (by norm_num : (0:ℝ)<1)
      (show 1<2*s by linarith)).of_nonneg_of_le (fun _ => by positivity)
    intro j
    calc
      _ ≤ ((j:ℝ)+1)^(-s)*((j:ℝ)+1)^(-s) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
            (by linarith)) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity : 0<(j:ℝ)+1)]; congr 1; ring
  apply Summable.of_add_one_of_neg_add_one
  · simpa only [twoScalePower_positive] using hp
  · simpa only [twoScalePower_neg,twoScalePower_positive] using hp

theorem tsum_twoScalePower (s : ℝ) (hs : (1:ℝ)/2 < s) (n : ℕ) :
    (∑' k : ℤ, twoScalePower s n k)=
      2*∑' j : ℕ, ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s) := by
  have h := summable_twoScalePower s hs n
  have hp := h.comp_injective (i := fun j : ℕ => (j:ℤ)+1) (by intro a b h; dsimp only at h; omega)
  have hn := h.comp_injective (i := fun j : ℕ => -((j:ℤ)+1)) (by intro a b h; dsimp only at h; omega)
  rw [tsum_of_add_one_of_neg_add_one hp hn]
  have hz : twoScalePower s n 0=0 := rfl
  simp only [twoScalePower_neg,twoScalePower_positive,hz,add_zero]
  ring

private theorem reciprocal_pair_twoScale (s N u v : ℝ) (hs : 0 ≤ s)
    (hN : 0 < N) (hu : 0 < u) (hv : 0 < v) (hmax : N ≤ max u v) :
    u^(-s)*v^(-s) ≤ (2:ℝ)^s*(u^(-s)*(N+u)^(-s)+v^(-s)*(N+v)^(-s)) := by
  have haux (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) (hNv : N ≤ v) :
      u^(-s)*v^(-s) ≤ (2:ℝ)^s*(u^(-s)*(N+u)^(-s)) := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < N+u)
      (show N+u ≤ 2*v by linarith) (neg_nonpos.mpr hs)
    have hvv : v^(-s)=(2:ℝ)^s*(2*v)^(-s) := by
      rw [Real.mul_rpow (by norm_num) hv.le,← mul_assoc,
        ← Real.rpow_add (by norm_num : (0:ℝ)<2),add_neg_cancel,Real.rpow_zero,one_mul]
    calc
      _ = (2:ℝ)^s*(u^(-s)*(2*v)^(-s)) := by rw [hvv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)
  rcases le_total u v with huv | hvu
  · exact (haux u v hu hv huv (by simpa only [max_eq_right huv] using hmax)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have h := haux v u hv hu hvu (by simpa only [max_eq_left hvu] using hmax)
    rw [mul_comm (v^(-s)) (u^(-s))] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity))

theorem quadraticPowerKernel_le_twoScale (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    quadraticPowerKernel s n k ≤ (2:ℝ)^s*
      (twoScalePower s n ((n:ℤ)+k)+twoScalePower s n ((n:ℤ)-k)) := by
  by_cases hk : k=(n:ℤ) ∨ k=-(n:ℤ)
  · simp only [quadraticPowerKernel,if_pos hk]
    unfold twoScalePower
    split_ifs <;> positivity
  have hp : (n:ℤ)+k≠0 := by omega
  have hm : (n:ℤ)-k≠0 := by omega
  have hup : 0 < |(n:ℝ)+(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hp)
  have hum : 0 < |(n:ℝ)-(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  have hmax : (n:ℝ) ≤ max |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)| := by
    have h := abs_add_le ((n:ℝ)+(k:ℝ)) ((n:ℝ)-(k:ℝ))
    rw [show (n:ℝ)+(k:ℝ)+((n:ℝ)-(k:ℝ))=2*n by ring,
      abs_of_nonneg (by positivity : 0≤2*(n:ℝ))] at h
    linarith [le_max_left |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)|,
      le_max_right |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)|]
  simpa only [quadraticPowerKernel,if_neg hk,twoScalePower,if_neg hp,if_neg hm,
    Int.cast_add,Int.cast_sub,Int.cast_natCast] using reciprocal_pair_twoScale s n _ _ hs
      (by exact_mod_cast hn) hup hum hmax

theorem quadraticPowerKernel_twoScale_bound (s : ℝ) (hs : (1:ℝ)/2 < s)
    (n : ℕ) (hn : 1 ≤ n) :
    Summable (quadraticPowerKernel s n) ∧
      (∑' k : ℤ, quadraticPowerKernel s n k) ≤
        (4*(2:ℝ)^s)*(∑' j : ℕ, ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)) := by
  have ht := summable_twoScalePower s hs n
  have hp := ht.comp_injective (Equiv.addLeft (n:ℤ)).injective
  have hm := ht.comp_injective (Equiv.subLeft (n:ℤ)).injective
  change Summable (fun k : ℤ => twoScalePower s n ((n:ℤ)+k)) at hp
  change Summable (fun k : ℤ => twoScalePower s n ((n:ℤ)-k)) at hm
  have hmajor := (hp.add hm).mul_left ((2:ℝ)^s)
  have hnonneg (k : ℤ) : 0 ≤ quadraticPowerKernel s n k := by
    unfold quadraticPowerKernel
    split_ifs <;> positivity
  have hpoint := quadraticPowerKernel_le_twoScale s (by linarith) n hn
  have hsum := hmajor.of_nonneg_of_le hnonneg hpoint
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' k : ℤ, (2:ℝ)^s*(twoScalePower s n ((n:ℤ)+k)+twoScalePower s n ((n:ℤ)-k)) :=
      hsum.tsum_le_tsum hpoint hmajor
    _ = _ := by
      have hps : (∑' k : ℤ, twoScalePower s n ((n:ℤ)+k))=∑' k : ℤ, twoScalePower s n k :=
        (Equiv.addLeft (n:ℤ)).tsum_eq (twoScalePower s n)
      have hms : (∑' k : ℤ, twoScalePower s n ((n:ℤ)-k))=∑' k : ℤ, twoScalePower s n k :=
        (Equiv.subLeft (n:ℤ)).tsum_eq (twoScalePower s n)
      rw [tsum_mul_left,hp.tsum_add hm,hps,hms,tsum_twoScalePower s hs n]
      ring

end NLS.ReciprocalSeries
