import NLS.KdV.HillEnergyProductEmbedding
import NLS.KdV.HillEnergyProductCutoffs
import NLS.ZakharovShabat.JointDeletedSingleSpectralProducts

/-! The literal deleted positive-energy product is jointly entire in
energy and the full inverse-index l2 zero displacement. Algebraic
single-root product coordinates supply its actual finite-cutoff limit. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergySequenceFactor (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ) : ℂ :=
  (((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*t.2 ⟨j+1,by omega⟩-t.1)/
    ((Real.pi:ℂ)*((j:ℂ)+1))^2

def hillEnergySequencePartialProduct (n : ℕ+) (N : ℕ)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  ∏ j ∈ (Finset.range N).erase ((n:ℕ)-1),hillEnergySequenceFactor t j

def hillEnergySequenceProduct (n : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  jointDeletedSingleSpectralProduct (p := 2) 0 (0,hillEnergyProductEmbedding n t)

theorem analyticAt_hillEnergySequenceProduct (n : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : AnalyticAt ℂ (hillEnergySequenceProduct n) t :=
  (analyticOnNhd_jointDeletedSingleSpectralProduct (by norm_num) (by norm_num) 0 _ (mem_univ _)).comp
    (f := fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 => (0,hillEnergyProductEmbedding n s))
    (analyticAt_const.prod (analyticAt_hillEnergyProductEmbedding n t))

theorem centered_deleted_single_partialProduct (a : Coeff 2)
    (ha : ∀ k : ℤ, k ≤ 0 → a k = 0) (N : ℕ) :
    jointDeletedSingleSpectralPartialProduct 0 N (0,a) =
      ∏ j ∈ Finset.range N, (1+a ((j:ℤ)+1)/((Real.pi:ℂ)*((j:ℂ)+1))) := by
  let F : ℤ → ℂ := fun k => if k = 0 then 1 else singleSpectralFactor (displacedRoots a) 0 k
  have h0 : (0:ℤ) ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by simp
  have he : jointDeletedSingleSpectralPartialProduct 0 N (0,a) =
      ∏ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),F k := by
    change (∏ k ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
      singleSpectralFactor (displacedRoots a) 0 k)/singleSpectralDenominator 0 = _
    rw [show singleSpectralDenominator 0 = 1 by simp [singleSpectralDenominator],div_one]
    have h := Finset.mul_prod_erase (Finset.Icc (-(N:ℤ)) (N:ℤ)) F h0
    have hF : F 0 = 1 := by simp [F]
    rw [hF,one_mul] at h
    rw [← h]
    apply Finset.prod_congr rfl
    intro k hk
    exact (if_neg (Finset.ne_of_mem_erase hk)).symm
  rw [he,prod_symmetric_interval]
  have hpos (j : ℕ) : F ((j:ℤ)+1) = 1+a ((j:ℤ)+1)/((Real.pi:ℂ)*((j:ℂ)+1)) := by
    simp only [F,if_neg (by omega : (j:ℤ)+1 ≠ 0),singleSpectralFactor,
      singleSpectralDenominator,displacedRoots,sub_zero,Int.cast_add,Int.cast_natCast,Int.cast_one]
    have hd : (Real.pi:ℂ)*((j:ℂ)+1) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Nat.cast_add_one_ne_zero j)
    field_simp
  have hneg (j : ℕ) : F (-((j:ℤ)+1)) = 1 := by
    simp only [F,if_neg (by omega : -((j:ℤ)+1) ≠ 0),singleSpectralFactor,
      singleSpectralDenominator,displacedRoots,sub_zero]
    rw [ha (-((j:ℤ)+1)) (by omega),add_zero]
    exact div_self (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Int.cast_ne_zero.mpr (by omega : -((j:ℤ)+1) ≠ 0)))
  simp only [hpos,hneg,mul_one]
  simp only [F,if_pos rfl,one_mul]

theorem hillEnergySequencePartialProduct_eq_embedding (n : ℕ+) (N : ℕ)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequencePartialProduct n N t =
      jointDeletedSingleSpectralPartialProduct 0 N (0,hillEnergyProductEmbedding n t) := by
  rw [centered_deleted_single_partialProduct _ (hillEnergyProductEmbedding_nonpos n t)]
  have hf (j : ℕ) : 1+hillEnergyProductEmbedding n t ((j:ℤ)+1)/((Real.pi:ℂ)*((j:ℂ)+1)) =
      if j = (n:ℕ)-1 then 1 else hillEnergySequenceFactor t j := by
    let m : ℕ+ := ⟨j+1,by omega⟩
    have he : (j:ℤ)+1 = ((m:ℕ):ℤ) := by change (j:ℤ)+1 = ((j+1:ℕ):ℤ); omega
    have hm : m = n ↔ j = (n:ℕ)-1 := by
      constructor
      · intro h; have h' := congrArg (fun r : ℕ+ => (r:ℕ)) h; dsimp [m] at h'; omega
      · intro h; apply Subtype.ext; change j+1 = (n:ℕ); have hn := n.pos; omega
    rw [he,hillEnergyProductEmbedding_positive]
    simp only [hm]
    by_cases hj : j = (n:ℕ)-1
    · simp only [if_pos hj,zero_div,add_zero]
    · simp only [if_neg hj,hillEnergySequenceFactor]
      have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hcast : ((m:ℕ):ℂ) = (j:ℂ)+1 := by dsimp [m]; push_cast; rfl
      rw [hcast]
      have hd : (j:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero j
      field_simp
      ring
  simp only [hf]
  unfold hillEnergySequencePartialProduct
  by_cases hn : (n:ℕ)-1 ∈ Finset.range N
  · rw [← Finset.insert_erase hn,Finset.prod_insert (Finset.notMem_erase _ _)]
    simp only [ite_true,one_mul,Finset.erase_insert_eq_erase,Finset.erase_idem]
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  · rw [Finset.erase_eq_of_notMem hn]
    apply Finset.prod_congr rfl
    intro j hj
    have hjn : j ≠ (n:ℕ)-1 := fun h => hn (h ▸ hj)
    rw [if_neg hjn]

theorem tendsto_hillEnergySequencePartialProduct (n : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    Tendsto (fun N => hillEnergySequencePartialProduct n N t) atTop (𝓝 (hillEnergySequenceProduct n t)) := by
  simp_rw [hillEnergySequencePartialProduct_eq_embedding]
  exact tendsto_jointDeletedSingleSpectralPartialProduct (by norm_num) (by norm_num) 0 _

theorem exists_uniform_hillEnergySequenceProduct_neighborhood (n : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    ∃ U : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2), IsOpen U ∧ t ∈ U ∧
      TendstoUniformlyOn (hillEnergySequencePartialProduct n) (hillEnergySequenceProduct n) atTop U := by
  let R := ‖hillEnergyProductEmbedding n t‖+1
  let U := {s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 | ‖hillEnergyProductEmbedding n s‖ < R}
  have hcont : Continuous (hillEnergyProductEmbedding n) :=
    continuous_iff_continuousAt.mpr (fun s => (analyticAt_hillEnergyProductEmbedding n s).continuousAt)
  refine ⟨U,isOpen_lt hcont.norm continuous_const,by change ‖hillEnergyProductEmbedding n t‖ < R; dsimp [R]; linarith,?_⟩
  have h := (tendstoUniformlyOn_jointDeletedSingleSpectralProduct (by norm_num) (by norm_num) 0
    ({0}:Set ℂ) isCompact_singleton (closedBall (0:Coeff 2) R) R (by dsimp [R]; positivity)
    (fun a ha => by simpa only [mem_closedBall,dist_zero_right] using ha)).comp
      (fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 => (0,hillEnergyProductEmbedding n s))
  have hu := h.mono (show U ⊆ (fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 =>
      (0,hillEnergyProductEmbedding n s)) ⁻¹' (({0}:Set ℂ) ×ˢ closedBall (0:Coeff 2) R) from
    fun s hs => ⟨mem_singleton _,by
      change dist (hillEnergyProductEmbedding n s) 0 ≤ R
      rw [dist_zero_right]
      exact le_of_lt hs⟩)
  simpa only [Function.comp_def,← hillEnergySequencePartialProduct_eq_embedding,hillEnergySequenceProduct] using! hu

end NLS.KdV
