import NLS.Articles.KdVKdV2Frequencies.NativeCorrectionHilbertControl
import NLS.SequenceSpaces.HilbertControlledAnalyticSeries
import NLS.KdV.HillSummedRegularCorrection

/-! # The actual infinite regular correction phase is natively Hilbert analytic

The actual correction vectors form an absolutely convergent Bochner series.
One complex period-one L2 ball precedes every gap, source and output index.
Its positive components recover the existing physical summed corrections.
-/
noncomputable section
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillPhysical_native_summed_regular_corrections :
    ∃ η : ℝ, ∃ Φ : Coeff 2 → Coeff 2, ∃ M : ℝ,
      0 < η ∧ 0 < M ∧ AnalyticOnNhd ℂ Φ (ball (0 : Coeff 2) η) ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ‖Φ u‖ ≤ M ∧ ∀ j : ℤ, j ≤ 0 → Φ u j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ n : ℕ+, Φ u (n : ℤ) = hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property := by
  obtain ⟨η,β,a,A,B,hη,hA,hB,_,ha,hβ,hphysical⟩ :=
    exists_hillPhysical_native_regular_correction_hilbert_control
  let f := fun (j : ℤ) (u : Coeff 2) => if hj : 0 < j then β (Coeff.positivePoleIndex j hj) u else 0
  let d := Coeff.positivePuncturedLattice 2 (by norm_num)
  have hf (j : ℤ) : AnalyticOnNhd ℂ (f j) (ball (0 : Coeff 2) η) := by
    by_cases hj : 0 < j
    · simpa only [f,dif_pos hj] using (hβ (Coeff.positivePoleIndex j hj)).1
    · simpa only [f,dif_neg hj] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : Coeff 2 => (0 : Coeff 2)) (ball 0 η))
  have hcontrol (u : Coeff 2) (hu : u ∈ ball 0 η) (j : ℤ) :
      ‖f j u‖ ≤ A*‖a u j‖*‖d j‖ := by
    by_cases hj : 0 < j
    · let k := Coeff.positivePoleIndex j hj
      have hk : (k : ℤ) = j := by
        change (j.toNat : ℤ) = j
        exact Int.toNat_of_nonneg hj.le
      have hkr : (k : ℝ) = j := Coeff.positivePoleIndex_real j hj
      have hd : ‖d j‖ = 1/(k : ℝ) := by
        rw [Coeff.positivePuncturedLattice_apply,if_pos hj,norm_inv]
        rw [show (j : ℂ) = ((j : ℝ) : ℂ) by norm_cast,norm_real,Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast hj : (0 : ℝ) < j),hkr,one_div]
      have h := ((hβ k).2 u hu).1
      rw [hk] at h
      dsimp only [f]
      rw [dif_pos hj]
      exact h.trans_eq (by rw [hd]; ring)
    · dsimp only [f]
      rw [dif_neg hj,norm_zero]
      positivity
  obtain ⟨hs,hΦ,hbound⟩ := Coeff.analytic_tsum_of_hilbert_control f a d isOpen_ball hf A B hA.le ha hcontrol
  let Φ := fun u : Coeff 2 => ∑' j : ℤ, f j u
  have heval (u : Coeff 2) (hu : u ∈ ball 0 η) (n : ℤ) : Φ u n = ∑' j : ℤ, f j u n :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).map_tsum (hs u hu).of_norm
  have hnat (k : ℕ+) (u : Coeff 2) : f (k : ℤ) u = β k u := by
    dsimp only [f]
    rw [dif_pos (by exact_mod_cast k.pos)]
    congr 1
  refine ⟨η,Φ,2*A*B,hη,by positivity,hΦ,?_,?_⟩
  · intro u hu
    refine ⟨(hbound u hu).trans ?_,?_⟩
    · have hd : ‖d‖ ≤ 2 := Coeff.norm_positivePuncturedLattice_two_le
      exact (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ A*B)).trans_eq (by ring)
    · intro n hn
      rw [heval u hu n]
      have hz (j : ℤ) : f j u n = 0 := by
        by_cases hj : 0 < j
        · dsimp only [f]
          rw [dif_pos hj]
          exact ((hβ (Coeff.positivePoleIndex j hj)).2 u hu).2 n hn
        · simp only [f,dif_neg hj,lp.coeFn_zero,Pi.zero_apply]
      simp only [hz,tsum_zero]
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ n : ℕ+, Φ u (n : ℤ) = hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property
    intro n
    rw [heval u hp]
    rw [tsum_eq_positive_of_nonpositive_zero _ (by
      intro j hj
      simp only [f,dif_neg (by omega : ¬ 0 < j),lp.coeFn_zero,Pi.zero_apply])]
    simp_rw [hnat]
    have he := hphysical p hp
    change ∀ k n : ℕ+, β k u (n : ℤ) =
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property at he
    simp_rw [he]
    exact (Equiv.pnatEquivNat.symm.tsum_eq (fun k : ℕ+ =>
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property)).symm

end NLS.Articles.KdVKdV2Frequencies
