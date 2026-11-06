import NLS.KdV.HillProductPeriodParameterLimit
import NLS.KdV.HillComplexTailPeriodAnalytic
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.CompactTailCoordinateDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original full-product complex-minus-free period error with the
original limiting mixed-period scaling. -/
def hillFullComplexPeriodError (k : ℕ) (t : Coeff 2 × Coeff 2) : ℂ :=
  (-2*(Real.pi : ℂ))*(hillAbelianProductComplexPeriod 0 h0q h0r 0 k t-
    hillAbelianProductComplexPeriod 0 h0q h0r 0 k (t.1,0))

theorem norm_hillFullComplexPeriodError_le_of_control
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (a p : Coeff 2) (hp : ‖p‖≤B) (k : ℕ) (hk : N≤k) :
    ‖hillFullComplexPeriodError h0q h0r k (a,p)‖≤D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ) := by
  have hk1 : 1≤k := hN.trans hk
  have hdp := (hc p hp).1 k hk
  have hd0 (E : ℂ) (hE : E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
      (E,(0:Coeff 2))∈hillAbelianComplexRootDomain 0 h0q h0r := by
    simpa only [map_zero] using mem_hillAbelianComplexRootDomain_base 0 h0q h0r E
      (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
  have ht := (tendsto_scaled_hillAbelianComplexPeriod_full_at_parameter 0 h0q h0r k hk1 a p hdp).sub
    (tendsto_scaled_hillAbelianComplexPeriod_full_at_parameter 0 h0q h0r k hk1 a 0 hd0)
  simp_rw [←mul_sub] at ht
  have he (n : ℕ) : hillAbelianComplexPeriod 0 h0q h0r n k (a,0)=hillAbelianHilbertPeriod 0 h0q h0r n k a := by
    simpa only [map_zero] using hillAbelianComplexPeriod_at_base 0 h0q h0r n k hk1 a
  simp only [he] at ht
  apply le_of_tendsto ht.norm
  filter_upwards [eventually_ge_atTop (k+1)] with n hn
  exact (hc p hp).2 n k (by omega) hk (by omega) a

def hillFullComplexPeriodErrorCoordinate (N : ℕ) (t : Coeff 2 × Coeff 2) (m : ℤ) : ℂ :=
  if 0<m ∧ N≤m.toNat then hillFullComplexPeriodError h0q h0r m.toNat t else 0

def hillFullComplexPeriodErrorSequence (N : ℕ) (t : Coeff 2 × Coeff 2) : Coeff 2 :=
  Coeff.ofFunctionOrZero 2 (hillFullComplexPeriodErrorCoordinate h0q h0r N t)

theorem norm_hillFullComplexPeriodErrorCoordinate_le
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (a p : Coeff 2) (hp : ‖p‖≤B) (m : ℤ) :
    ‖hillFullComplexPeriodErrorCoordinate h0q h0r N (a,p) m‖≤
      (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
  unfold hillFullComplexPeriodErrorCoordinate
  by_cases hm : 0<m ∧ N≤m.toNat
  · rw [if_pos hm]
    have hh := norm_hillFullComplexPeriodError_le_of_control h0q h0r N hN B D hc a p hp m.toNat hm.2
    have hcast : (m.toNat : ℤ)=m := by omega
    have hmt : 1≤m.toNat := by omega
    have hlat := Coeff.positivePuncturedLattice_natSucc 2 (by norm_num) (m.toNat-1)
    rw [Nat.sub_add_cancel hmt,hcast] at hlat
    simpa only [div_eq_mul_inv,hlat,norm_inv,norm_natCast] using hh
  · rw [if_neg hm,norm_zero]
    positivity

private theorem hillFullComplexPeriodErrorCoordinate_mem
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (a p : Coeff 2) (hp : ‖p‖≤B) : Memℓp (hillFullComplexPeriodErrorCoordinate h0q h0r N (a,p)) 2 := by
  apply ((lp.memℓp (Coeff.positivePuncturedLattice 2 (by norm_num))).norm.const_mul
    (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)).mono
  exact norm_hillFullComplexPeriodErrorCoordinate_le h0q h0r N hN B D hD hc a p hp

theorem hillFullComplexPeriodErrorSequence_apply
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (a p : Coeff 2) (hp : ‖p‖≤B) (m : ℤ) :
    hillFullComplexPeriodErrorSequence h0q h0r N (a,p) m=hillFullComplexPeriodErrorCoordinate h0q h0r N (a,p) m :=
  Coeff.ofFunctionOrZero_apply_of_mem 2 _ (hillFullComplexPeriodErrorCoordinate_mem h0q h0r N hN B D hD hc a p hp) m

theorem norm_hillFullComplexPeriodErrorSequence_le
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (a p : Coeff 2) (hp : ‖p‖≤B) :
    ‖hillFullComplexPeriodErrorSequence h0q h0r N (a,p)‖≤2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  let C := D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖
  have hC : 0≤C := by dsimp only [C];positivity
  have hh : ‖hillFullComplexPeriodErrorSequence h0q h0r N (a,p)‖≤‖(C : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0)
    intro m
    rw [hillFullComplexPeriodErrorSequence_apply h0q h0r N hN B D hD hc a p hp]
    simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using
      norm_hillFullComplexPeriodErrorCoordinate_le h0q h0r N hN B D hD hc a p hp m
  rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hC] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left Coeff.norm_positivePuncturedLattice_two_le hC)).trans_eq (by dsimp only [C];ring)

theorem analyticOnNhd_hillFullComplexPeriodErrorSequence
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hB : 0<B) (hD : 0≤D) (hc : HillComplexTailPeriodControl h0q h0r N B D) :
    AnalyticOnNhd ℂ (hillFullComplexPeriodErrorSequence h0q h0r N) (univ ×ˢ ball (0:Coeff 2) B) := by
  let U : Set (Coeff 2 × Coeff 2) := univ ×ˢ ball 0 B
  have hU : IsOpen U := isOpen_univ.prod isOpen_ball
  have hpB (p : Coeff 2) (hp : p∈ball 0 B) : ‖p‖≤B :=
    (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hp).le
  have hraw (m : ℤ) : AnalyticOnNhd ℂ (fun t => hillFullComplexPeriodErrorCoordinate h0q h0r N t m) U := by
    by_cases hm : 0<m ∧ N≤m.toNat
    · have hk : 1≤m.toNat := hN.trans hm.2
      have hP := analyticOnNhd_hillAbelianProductComplexPeriod_of_domain 0 h0q h0r 0 m.toNat hk (ball 0 B) isOpen_ball
        (fun p hp => (hc p (hpB p hp)).1 m.toNat hm.2)
      intro t ht
      have hzero := (hP (t.1,0) ⟨mem_univ _,mem_ball_self hB⟩).comp
        (f := fun u : Coeff 2 × Coeff 2 => (u.1,0)) (analyticAt_fst.prod analyticAt_const)
      have hh : AnalyticAt ℂ (hillFullComplexPeriodError h0q h0r m.toNat) t :=
        analyticAt_const.mul ((hP t ht).sub hzero)
      simpa only [hillFullComplexPeriodErrorCoordinate,if_pos hm] using hh
    · have he : (fun t : Coeff 2 × Coeff 2 => hillFullComplexPeriodErrorCoordinate h0q h0r N t m)=fun _ => 0 := by
        funext t
        exact if_neg hm
      rw [he]
      exact analyticOnNhd_const
  have hlocal (t : Coeff 2 × Coeff 2) (ht : t∈U) :
      ∃ V : Set (Coeff 2 × Coeff 2), IsOpen V ∧ t∈V ∧ V⊆U ∧ ∃ M : ℝ,
        ∀ u∈V, ∃ b : Coeff 2, (∀ m, b m=hillFullComplexPeriodErrorCoordinate h0q h0r N u m) ∧ ‖b‖≤M := by
    let R := ‖t.1‖+1
    let M := 2*D*Real.exp ((8/Real.pi^2)*R)*B
    refine ⟨ball t.1 1 ×ˢ ball 0 B,isOpen_ball.prod isOpen_ball,⟨mem_ball_self (by norm_num),ht.2⟩,
      (fun _ hu => ⟨mem_univ _,hu.2⟩),M,?_⟩
    intro u hu
    refine ⟨hillFullComplexPeriodErrorSequence h0q h0r N u,
      (fun m => hillFullComplexPeriodErrorSequence_apply h0q h0r N hN B D hD hc u.1 u.2 (hpB u.2 hu.2) m),?_⟩
    have hd : ‖u.1-t.1‖<1 := by simpa only [mem_ball,dist_eq_norm] using hu.1
    have hR : ‖u.1‖≤R := (norm_le_norm_sub_add u.1 t.1).trans (by dsimp only [R];linarith)
    exact (norm_hillFullComplexPeriodErrorSequence_le h0q h0r N hN B D hD hc u.1 u.2 (hpB u.2 hu.2)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR (by positivity)))
        (by positivity : 0≤2*D)) (hpB u.2 hu.2) (norm_nonneg _) (by positivity))
  exact (Coeff.analytic_realization_of_local_bounds (fun t m => hillFullComplexPeriodErrorCoordinate h0q h0r N t m) hU hraw hlocal).2

theorem isCompactOperator_fderiv_hillFullComplexPeriodErrorSequence
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hB : 0<B) (hD : 0≤D) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (a p : Coeff 2) (hp : ‖p‖<B) :
    IsCompactOperator (fderiv ℂ (fun b : Coeff 2 => hillFullComplexPeriodErrorSequence h0q h0r N (b,p)) a) := by
  let f : Coeff 2 → Coeff 2 := fun b => hillFullComplexPeriodErrorSequence h0q h0r N (b,p)
  have hfa : AnalyticOnNhd ℂ f univ := by
    intro b _
    exact (analyticOnNhd_hillFullComplexPeriodErrorSequence h0q h0r N hN B D hB hD hc (b,p)
      ⟨mem_univ _,by simpa only [mem_ball,dist_zero_right] using hp⟩).comp
      (f := fun b : Coeff 2 => (b,p)) (analyticAt_id.prod analyticAt_const)
  let C := D*Real.exp ((8/Real.pi^2)*(‖a‖+2))*‖p‖
  let b : Coeff 2 := (C : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)
  apply Coeff.isCompactOperator_fderiv_of_tailCoordinateBound (by norm_num : (2:ℝ≥0∞)≠⊤)
    f a 1 (by norm_num) (hfa.differentiableOn.mono (subset_univ _)) b ∅
  intro m _ v hv
  have hd : ‖v-a‖<2 := by simpa only [mem_ball,dist_eq_norm,show (1:ℝ)+1=2 by norm_num] using hv
  have hva : ‖v‖≤‖a‖+2 := (norm_le_norm_sub_add v a).trans (by linarith)
  change ‖hillFullComplexPeriodErrorSequence h0q h0r N (v,p) m‖≤‖b m‖
  rw [hillFullComplexPeriodErrorSequence_apply h0q h0r N hN B D hD hc v p hp.le]
  have hnorm : ‖b m‖=C*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0≤C by dsimp only [C];positivity)]
  rw [hnorm]
  apply (norm_hillFullComplexPeriodErrorCoordinate_le h0q h0r N hN B D hD hc v p hp.le m).trans
  dsimp only [C]
  gcongr

end NLS.KdV
