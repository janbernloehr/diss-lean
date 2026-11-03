import NLS.SequenceSpaces.PositiveCartesianParameters

/-! # Modal tests for continuous cotangents on a native Cartesian target -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def positiveCartesianInsert (n : ℤ) (v : ℂ × ℂ) : PositiveCartesianTarget w p :=
  positiveCartesianParameterMap w p (lp.single p n ((w n : ℂ)*v.1),lp.single p n ((w n : ℂ)*v.2))

theorem positiveCartesianInsert_eval (n : ℤ) (hn : 0 < n) (k : ℤ) (v : ℂ × ℂ) :
    positiveCartesianEval w p k (positiveCartesianInsert w p n v) = if k = n then v else 0 := by
  rw [positiveCartesianInsert,positiveCartesianParameterMap_eval]
  by_cases hkn : k = n
  · subst k
    simp [hn,lp.single_apply,w.complex_ne_zero]
  · simp [hkn,lp.single_apply]

theorem positiveCartesianInsert_mean (n : ℤ) (hn : 0 < n) (v : ℂ × ℂ) :
    (positiveCartesianInsert w p n v).2 = 0 := by
  simp [positiveCartesianInsert,positiveCartesianParameterMap_mean,lp.single_apply,
    (ne_of_gt hn).symm]

theorem positiveCartesianInsert_decomposition (n : ℤ) (hn : 0 < n) (v : ℂ × ℂ) :
    positiveCartesianInsert w p n v =
      v.1 • positiveCartesianInsert w p n (1,0)+v.2 • positiveCartesianInsert w p n (0,1) := by
  apply positivePairMean_ext
  · intro k _
    change positiveCartesianEval w p k (positiveCartesianInsert w p n v) =
      positiveCartesianEval w p k (v.1 • positiveCartesianInsert w p n (1,0)+v.2 • positiveCartesianInsert w p n (0,1))
    rw [map_add,map_smul,map_smul,positiveCartesianInsert_eval w p n hn,
      positiveCartesianInsert_eval w p n hn,positiveCartesianInsert_eval w p n hn]
    split_ifs <;> simp
  · change (positiveCartesianInsert w p n v).2 =
      v.1*(positiveCartesianInsert w p n (1,0)).2+v.2*(positiveCartesianInsert w p n (0,1)).2
    rw [positiveCartesianInsert_mean w p n hn,positiveCartesianInsert_mean w p n hn,
      positiveCartesianInsert_mean w p n hn]
    simp

theorem cotangent_positiveCartesianInsert
    (L : PositiveCartesianTarget w p →L[ℂ] ℂ) (n : ℤ) (hn : 0 < n) (v : ℂ × ℂ) :
    L (positiveCartesianInsert w p n v) =
      L (positiveCartesianInsert w p n (1,0))*v.1+L (positiveCartesianInsert w p n (0,1))*v.2 := by
  rw [positiveCartesianInsert_decomposition w p n hn v,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

theorem positiveCartesianActionVector_eq_insert (n : ℤ) (hn : 0 < n) (z : PositiveCartesianTarget w p) :
    positiveCartesianActionVector w p n z = positiveCartesianInsert w p n
      ((positiveCartesianEval w p n z).2,-(positiveCartesianEval w p n z).1) := by
  apply positivePairMean_ext
  · intro k _
    change positiveCartesianEval w p k (positiveCartesianActionVector w p n z) =
      positiveCartesianEval w p k (positiveCartesianInsert w p n
        ((positiveCartesianEval w p n z).2,-(positiveCartesianEval w p n z).1))
    rw [positiveCartesianActionVector_eval,positiveCartesianInsert_eval w p n hn]
    split_ifs with hkn
    · subst k
      rfl
    · rfl
  · change (0 : ℂ) = (positiveCartesianInsert w p n _).2
    exact (positiveCartesianInsert_mean w p n hn _).symm

theorem cotangent_eq_zero_of_modes_of_mean_zero (hp : p ≠ ⊤)
    (L : PositiveCartesianTarget w p →L[ℂ] ℂ) (z : PositiveCartesianTarget w p)
    (hz : z.2 = 0)
    (hmodes : ∀ n : ℤ, 0 < n → L (positiveCartesianInsert w p n (positiveCartesianEval w p n z)) = 0) :
    L z = 0 := by
  let b := positiveCartesianParameterSection w p z
  have hs := (L.comp (positiveCartesianParameterMap w p)).hasSum
    ((lp.hasSum_single hp b.1).prodMk (lp.hasSum_single hp b.2))
  change HasSum (fun n : ℤ => L (positiveCartesianParameterMap w p
    (lp.single p n (b.1 n),lp.single p n (b.2 n))))
      (L (positiveCartesianParameterMap w p b)) at hs
  have he (n : ℤ) : L (positiveCartesianParameterMap w p
      (lp.single p n (b.1 n),lp.single p n (b.2 n))) = 0 := by
    by_cases hn : 0 < n
    · have hb₁ : b.1 n = (w n : ℂ)*z.1.1.val.val n := by
        simp only [b,positiveCartesianParameterSection_fst,if_neg (ne_of_gt hn),add_zero]
      have hb₂ : b.2 n = (w n : ℂ)*z.1.2.val.val n := positiveCartesianParameterSection_snd w p z n
      rw [hb₁,hb₂]
      exact hmodes n hn
    · have hx := z.1.1.property n (by omega)
      have hy := z.1.2.property n (by omega)
      have hb₁ : b.1 n = 0 := by simp [b,positiveCartesianParameterSection_fst,hx,hz]
      have hb₂ : b.2 n = 0 := by simp [b,positiveCartesianParameterSection_snd,hy]
      rw [hb₁,hb₂]
      simp only [lp.single_zero]
      change L (positiveCartesianParameterMap w p (0 : Coeff p × Coeff p)) = 0
      rw [map_zero,map_zero]
  simp only [he] at hs
  have hzero := hs.unique hasSum_zero
  simpa only [b,positiveCartesianParameterMap_section] using hzero

theorem cotangent_value_of_modes_except (hp : p ≠ ⊤)
    (L : PositiveCartesianTarget w p →L[ℂ] ℂ) (z : PositiveCartesianTarget w p)
    (hz : z.2 = 0) (n : ℤ) (hn : 0 < n)
    (hmodes : ∀ k : ℤ, 0 < k → k ≠ n →
      L (positiveCartesianInsert w p k (positiveCartesianEval w p k z)) = 0) :
    L z = L (positiveCartesianInsert w p n (positiveCartesianEval w p n z)) := by
  let e := positiveCartesianInsert w p n (positiveCartesianEval w p n z)
  have hmean : (z-e).2 = 0 := by
    change z.2-e.2 = 0
    rw [hz,positiveCartesianInsert_mean w p n hn,sub_self]
  have hzero := cotangent_eq_zero_of_modes_of_mean_zero w p hp L (z-e) hmean (by
    intro k hk
    rw [map_sub,positiveCartesianInsert_eval w p n hn]
    by_cases hkn : k = n
    · subst k
      simp only [ite_true,sub_self]
      rw [cotangent_positiveCartesianInsert w p L n hn]
      simp
    · rw [if_neg hkn,sub_zero]
      exact hmodes k hk hkn)
  rw [map_sub,sub_eq_zero] at hzero
  exact hzero

theorem cotangent_eq_mean_of_modal_zero (hp : p ≠ ⊤)
    (L : PositiveCartesianTarget w p →L[ℂ] ℂ)
    (hmodes : ∀ n : ℤ, 0 < n → L (positiveCartesianInsert w p n (1,0)) = 0 ∧
      L (positiveCartesianInsert w p n (0,1)) = 0) (z : PositiveCartesianTarget w p) :
    L z = z.2*L (0,1) := by
  let e : PositiveCartesianTarget w p := (0,1)
  have hz : (z-z.2 • e).2 = 0 := by
    change z.2-z.2*1 = 0
    ring
  have hzero := cotangent_eq_zero_of_modes_of_mean_zero w p hp L (z-z.2 • e) hz (by
    intro n hn
    rw [cotangent_positiveCartesianInsert w p L n hn,(hmodes n hn).1,(hmodes n hn).2]
    simp)
  change L (z-z.2 • e) = 0 at hzero
  rw [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at hzero
  exact hzero

end NLS.WeightedCoeff
