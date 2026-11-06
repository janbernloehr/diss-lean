import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! # Uniform same-order and lower-order mass majorants for triangular hierarchy recurrences. -/

noncomputable section
set_option autoImplicit false
namespace NLS.SequenceSpaces
theorem hierarchy_mass_product_le (x : ℝ) (hx : 0 ≤ x) (i k m : ℕ)
    (hik : i+k+1 ≤ m) :
    ((1+x)^i*x)*((1+x)^k*x) ≤ (1+x)^m*x := by
  have hp : 1 ≤ 1+x := by linarith
  calc
    _ = (1+x)^(i+k)*(x*x) := by rw [pow_add]; ring
    _ ≤ (1+x)^(i+k)*((1+x)*x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith : x ≤ 1+x) hx) (by positivity)
    _ = (1+x)^(i+k+1)*x := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp hik) hx

theorem exists_hierarchy_action_majorant (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A b : ℕ → ℝ,
      (∀ j, j ≤ m → 0 ≤ A j) →
      (∀ i j, i ≤ j → j ≤ m → A i ≤ A j) →
      (∀ j, j ≤ m → 0 ≤ b j) →
      (∀ j, j ≤ m → b j ≤ D j*(A j+(1+A 0)^j*A 0)+
        2*(if 2 ≤ j then ∑ ik ∈ Finset.antidiagonal (j-2), b ik.1*b ik.2 else 0)) →
      b m ≤ C*(1+A m)^m*A m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    let C : ℕ → ℝ := fun j => if hj : j < m then (ih j hj).choose else 0
    have hC (j : ℕ) : 0 ≤ C j := by
      dsimp only [C]
      split_ifs with hj
      · exact (ih j hj).choose_spec.1
      · exact le_rfl
    let S : ℝ := ∑ ik ∈ Finset.antidiagonal (m-2), C ik.1*C ik.2
    have hS : 0 ≤ S := Finset.sum_nonneg (fun ik _ => mul_nonneg (hC _) (hC _))
    refine ⟨2*D m+2*S, add_nonneg (mul_nonneg (by norm_num) (hD m)) (mul_nonneg (by norm_num) hS), ?_⟩
    intro A b hA hmono hb hbound
    have hAm := hA m le_rfl
    have hA0 := hA 0 (Nat.zero_le m)
    have h0m := hmono 0 m (Nat.zero_le m) le_rfl
    have hpow : (1+A 0)^m ≤ (1+A m)^m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have hbase : A m+(1+A 0)^m*A 0 ≤ 2*((1+A m)^m*A m) := by
      have h1 := one_le_pow₀ (show 1 ≤ 1+A m by linarith) (n := m)
      have he := mul_le_mul hpow h0m hA0 (by positivity : 0 ≤ (1+A m)^m)
      have hf := mul_le_mul_of_nonneg_right h1 hAm
      nlinarith
    have hlower (j : ℕ) (hj : j < m) : b j ≤ C j*(1+A j)^j*A j := by
      have ht := (ih j hj).choose_spec.2 A b
        (fun k hk => hA k (by omega))
        (fun k l hkl hl => hmono k l hkl (by omega))
        (fun k hk => hb k (by omega))
        (fun k hk => hbound k (by omega))
      simpa only [C, dif_pos hj] using ht
    have hconv : (if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), b ik.1*b ik.2 else 0) ≤
        S*((1+A m)^m*A m) := by
      split_ifs with hm
      · dsimp only [S]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro ik hik
        have he := Finset.mem_antidiagonal.mp hik
        have hi : ik.1 < m := by omega
        have hk : ik.2 < m := by omega
        have him := hmono ik.1 m (by omega) le_rfl
        have hkm := hmono ik.2 m (by omega) le_rfl
        have hbi : b ik.1 ≤ C ik.1*((1+A m)^ik.1*A m) := by
          calc
            _ ≤ C ik.1*(1+A ik.1)^ik.1*A ik.1 := hlower _ hi
            _ ≤ _ := by
              have hp := mul_le_mul
                (pow_le_pow_left₀ (show 0 ≤ 1+A ik.1 by linarith [hA ik.1 (by omega)])
                  (show 1+A ik.1 ≤ 1+A m by linarith) ik.1)
                him (hA ik.1 (by omega)) (by positivity : 0 ≤ (1+A m)^ik.1)
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (hC ik.1)
        have hbk : b ik.2 ≤ C ik.2*((1+A m)^ik.2*A m) := by
          calc
            _ ≤ C ik.2*(1+A ik.2)^ik.2*A ik.2 := hlower _ hk
            _ ≤ _ := by
              have hp := mul_le_mul
                (pow_le_pow_left₀ (show 0 ≤ 1+A ik.2 by linarith [hA ik.2 (by omega)])
                  (show 1+A ik.2 ≤ 1+A m by linarith) ik.2)
                hkm (hA ik.2 (by omega)) (by positivity : 0 ≤ (1+A m)^ik.2)
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (hC ik.2)
        calc
          _ ≤ (C ik.1*((1+A m)^ik.1*A m))*(C ik.2*((1+A m)^ik.2*A m)) :=
            mul_le_mul hbi hbk (hb ik.2 (by omega))
              (mul_nonneg (hC ik.1) (mul_nonneg (by positivity) hAm))
          _ = (C ik.1*C ik.2)*(((1+A m)^ik.1*A m)*((1+A m)^ik.2*A m)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hierarchy_mass_product_le (A m) hAm _ _ m (by omega))
            (mul_nonneg (hC _) (hC _))
      · exact mul_nonneg hS (by positivity)
    have ht := hbound m le_rfl
    have hd := mul_le_mul_of_nonneg_left hbase (hD m)
    nlinarith

theorem hierarchy_mass_mono (x y C : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hC : 0 ≤ C) (m : ℕ) : C*(1+x)^m*x ≤ C*((1+y)^m*y) := by
  have hy : 0 ≤ y := hx.trans hxy
  have h := mul_le_mul
    (pow_le_pow_left₀ (show 0 ≤ 1+x by linarith) (show 1+x ≤ 1+y by linarith) m)
    hxy hx (by positivity : 0 ≤ (1+y)^m)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hC

theorem exists_hierarchy_action_majorant_lower (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A b : ℕ → ℝ,
      (∀ j, j ≤ m → 0 ≤ A j) →
      (∀ i j, i ≤ j → j ≤ m → A i ≤ A j) →
      (∀ j, j ≤ m → 0 ≤ b j) →
      (∀ j, j ≤ m → b j ≤ D j*(A j+(1+A 0)^j*A 0)+
        2*(if 2 ≤ j then ∑ ik ∈ Finset.antidiagonal (j-2), b ik.1*b ik.2 else 0)) →
      b m ≤ C*(A m+(1+A (m-1))^m*A (m-1)) := by
  let C : ℕ → ℝ := fun j => (exists_hierarchy_action_majorant D hD j).choose
  have hC (j : ℕ) : 0 ≤ C j := (exists_hierarchy_action_majorant D hD j).choose_spec.1
  let S : ℝ := ∑ ik ∈ Finset.antidiagonal (m-2), C ik.1*C ik.2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun ik _ => mul_nonneg (hC _) (hC _))
  refine ⟨D m+2*S, add_nonneg (hD m) (mul_nonneg (by norm_num) hS), ?_⟩
  intro A b hA hmono hb hbound
  have hAm := hA m le_rfl
  have hB := hA (m-1) (by omega)
  have h0B := hmono 0 (m-1) (by omega) (by omega)
  have hlower (j : ℕ) (hj : j < m) : b j ≤ C j*((1+A (m-1))^j*A (m-1)) := by
    have ht := (exists_hierarchy_action_majorant D hD j).choose_spec.2 A b
      (fun k hk => hA k (by omega))
      (fun k l hkl hl => hmono k l hkl (by omega))
      (fun k hk => hb k (by omega))
      (fun k hk => hbound k (by omega))
    exact ht.trans (hierarchy_mass_mono (A j) (A (m-1)) (C j) (hA j (by omega))
      (hmono j (m-1) (by omega) (by omega)) (hC j) j)
  have herr : (1+A 0)^m*A 0 ≤ (1+A (m-1))^m*A (m-1) := by
    simpa only [one_mul] using hierarchy_mass_mono (A 0) (A (m-1)) 1
      (hA 0 (by omega)) h0B (by norm_num) m
  have hconv : (if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), b ik.1*b ik.2 else 0) ≤
      S*((1+A (m-1))^m*A (m-1)) := by
    split_ifs with hm2
    · dsimp only [S]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro ik hik
      have he := Finset.mem_antidiagonal.mp hik
      have hi : ik.1 < m := by omega
      have hk : ik.2 < m := by omega
      calc
        _ ≤ (C ik.1*((1+A (m-1))^ik.1*A (m-1)))*
            (C ik.2*((1+A (m-1))^ik.2*A (m-1))) :=
          mul_le_mul (hlower _ hi) (hlower _ hk) (hb ik.2 (by omega))
            (mul_nonneg (hC _) (mul_nonneg (by positivity) hB))
        _ = (C ik.1*C ik.2)*(((1+A (m-1))^ik.1*A (m-1))*
            ((1+A (m-1))^ik.2*A (m-1))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hierarchy_mass_product_le (A (m-1)) hB _ _ m (by omega))
          (mul_nonneg (hC _) (hC _))
    · exact mul_nonneg hS (by positivity)
  have ht := hbound m le_rfl
  have hd := mul_le_mul_of_nonneg_left herr (hD m)
  have hSA := mul_nonneg hS hAm
  nlinarith

end NLS.SequenceSpaces
