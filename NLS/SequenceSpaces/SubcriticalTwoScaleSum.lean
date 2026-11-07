import NLS.SequenceSpaces.SubcriticalPowerSum

/-! The sharp n^(1-2s) bound for a positive two-scale reciprocal series.
Its head uses the integrable power singularity and its tail the ordinary
summable 2s-power integral test. -/
noncomputable section
namespace NLS.ReciprocalSeries

theorem subcritical_twoScale_sum (s : ℝ) (hs : (1:ℝ)/2 < s) (hs1 : s < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun j : ℕ => ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)) ∧
      (∑' j : ℕ, ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)) ≤
        (1/(1-s)+1/(2*s-1))*(n:ℝ)^(1-2*s) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hsp : 0 < s := by linarith
  have htw : 1 < 2*s := by linarith
  let f := fun j : ℕ => ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)
  have hpower (j : ℕ) : f j ≤ ((j:ℝ)+1)^(-(2*s)) := by
    calc
      _ ≤ ((j:ℝ)+1)^(-s)*((j:ℝ)+1)^(-s) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
            (by linarith)) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < (j:ℝ)+1)]; congr 1; ring
  have hseries : Summable (fun j : ℕ => ((j:ℝ)+1)^(-(2*s))) :=
    summable_nat_shifted_rpow (by norm_num) htw
  have hf : Summable f := hseries.of_nonneg_of_le (fun _ => by dsimp [f]; positivity) hpower
  have hhead : (∑ j ∈ Finset.range n, f j) ≤
      (1/(1-s))*(n:ℝ)^(1-2*s) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (n:ℝ)^(-s)*((j:ℝ)+1)^(-s) := by
        apply Finset.sum_le_sum
        intro j _
        have h := Real.rpow_le_rpow_of_nonpos hnp
          (show (n:ℝ) ≤ (n:ℝ)+(j:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) j]) (neg_nonpos.mpr hsp.le)
        simpa only [f,mul_comm] using mul_le_mul_of_nonneg_left h
          (Real.rpow_nonneg (by positivity : 0 ≤ (j:ℝ)+1) (-s))
      _ = (n:ℝ)^(-s)*(∑ j ∈ Finset.range n, ((j:ℝ)+1)^(-s)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (n:ℝ)^(-s)*((n:ℝ)^(1-s)/(1-s)) :=
        mul_le_mul_of_nonneg_left (sum_range_succ_negative_power_le s hsp.le hs1 n) (by positivity)
      _ = _ := by
        rw [← mul_div_assoc,← Real.rpow_add hnp,show -s+(1-s)=1-2*s by ring]
        ring
  have htail : (∑' j : ℕ, f (j+n)) ≤ (1/(2*s-1))*(n:ℝ)^(1-2*s) := by
    calc
      _ ≤ ∑' j : ℕ, ((j:ℝ)+(n:ℝ)+1)^(-(2*s)) := by
        apply (hf.comp_injective (fun a b h => Nat.add_right_cancel h)).tsum_le_tsum
          (fun j => by simpa only [Function.comp_def,Nat.cast_add] using hpower (j+n))
          (summable_nat_shifted_rpow (by positivity : 0 < (n:ℝ)+1) htw |>.congr (fun j => by
            congr 1; ring))
      _ ≤ (n:ℝ)^(1-2*s)/(2*s-1) := by
        simpa only [zero_add] using tsum_nat_tail_shifted_rpow_le (α:=0) htw n (by simpa using hnp)
      _ = _ := by ring
  refine ⟨hf,?_⟩
  rw [← hf.sum_add_tsum_nat_add n]
  exact (add_le_add hhead htail).trans_eq (by ring)

end NLS.ReciprocalSeries
