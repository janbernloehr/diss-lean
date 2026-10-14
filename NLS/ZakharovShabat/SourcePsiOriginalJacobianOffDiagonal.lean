import NLS.ZakharovShabat.SourcePsiOriginalJacobianNonzero
import NLS.ZakharovShabat.SourcePsiOriginalEquationSup

/-!
# Uniform off-diagonal bounds on the original root domain

Original disk separation bounds the weighted Cauchy ratio in the
Jacobian contour formula. The gap numerator is controlled by three lp
displacement sequences. One common sequence therefore bounds every
weighted off-diagonal entry, uniformly in both the omitted index and
the column, including the entire finite head.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.originalJacobian_offDiagonal_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m k : ℤ)
    (hmn : m ≠ n) (hkn : k ≠ n) (hmk : m ≠ k)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (L : ℝ)
    (hb : ∀ z ∈ D m, ‖((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z‖ ≤ L) :
    ‖((m-k:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 n m k a ψ‖ ≤
      (2*Real.pi*(c*L))*(‖a m‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖) := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψV m d r hr he
  let f : ℂ → ℂ := fun z => ((m-k:ℤ):ℂ)*((displacedRoots a m-z)/(displacedRoots a k-z))*
    (((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z)
  have hZ := H.previous.quotients.originalZeta_analyticOnNhd hD ψ hψW hψV hreal n m hmn a ha d r hr he
  have hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact (analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr
        (hD.originalRootPlacement_avoids_closedBall a ha m k hmk.symm d r hr he z hz).symm))).mul
      (analyticAt_const.mul (hZ z hz))
  obtain ⟨z,hz,_,hbound,_⟩ := P.lemma12_3_circle f hf
  have hInt : (∮ z in C((d:ℂ),r), f z/sourceStandardRoot hp hp1 ψ m z) =
      ((m-k:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 n m k a ψ := by
    rw [H.originalJacobianEntry_contour hD ψ hψW hψV hreal n m k hmn hkn a ha d r hr he,
      ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr.le
    intro z _
    dsimp [f]
    ring
  have hnorm : ‖(2*(Real.pi:ℂ))⁻¹*
      (((m-k:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 n m k a ψ)‖ ≤ ‖f z‖ := by
    simpa only [PiecewiseC1Loop.integral_circle,P,SourceIsolatingNeighborhoods.periodCircle,hInt] using hbound
  have hzD := hD.gap ψ hψV m hz
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  have hsep := (hD.weighted_separation_closure k m hmk _ (ha k) z (subset_closure hzD)).2
  have heNorm : ‖((m-k:ℤ):ℂ)‖ = ‖((k-m:ℤ):ℂ)‖ := by
    simp only [Int.cast_sub]
    exact norm_sub_rev _ _
  have hfb : ‖f z‖ ≤
      (‖a m‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖)*(c*L) := by
    have hn : ‖f z‖ = ‖displacedRoots a m-z‖*
        (‖((k-m:ℤ):ℂ)‖/‖displacedRoots a k-z‖)*
        ‖((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z‖ := by
      simp only [f,norm_mul,norm_div,heNorm]
      ring
    rw [hn]
    exact (mul_le_mul (mul_le_mul (norm_displacedRoot_sub_gap_le hp hp1 a ψ m z hz)
      hsep (by positivity) (by positivity)) (hb z hzD) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hscale (w : ℂ) : ‖w‖ = (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹*w‖ := by
    rw [norm_mul,norm_inv,norm_mul]
    simp only [Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  rw [hscale]
  exact (mul_le_mul_of_nonneg_left (hnorm.trans hfb) (by positivity : 0 ≤ 2*Real.pi)).trans_eq (by ring)

theorem SourceLemma12_4Data.originalJacobian_offDiagonal_commonMajorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, IsRealType (CoeffPair.toMax p t.2) →
        t.1 ∈ sourcePsiOriginalRootPlacement D → ∃ B : Coeff p, ‖B‖ ≤ C ∧
          ∀ n m k : ℤ, m ≠ k →
            ‖((m-k:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 n m k t.1 t.2‖ ≤ ‖B m‖ := by
  classical
  obtain ⟨Uz,hUz,hbasez,hUV,K,C,hK,hC,hb⟩ :=
    H.previous.quotients.zeta_originalAsymptotic hW hD hV φ hφW hφV a₀
  obtain ⟨_,_,Vm,hVm,hφm,M,hM,hm⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  let U := Uz ∩ (ball a₀ 1 ×ˢ (Vm ∩ Vg))
  let L := Real.pi⁻¹+K+C
  let Q := 2*Real.pi*(c*L)
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨U,hUz.inter (isOpen_ball.prod (hVm.inter hVg)),
    ⟨hbasez,mem_ball_self (by norm_num),hφm,hφg⟩,(fun _ ht => hUV ht.1),
    Q*(‖a₀‖+1+M+G),by positivity,?_⟩
  intro t ht hreal ha
  have hZ (n m : ℤ) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ D m) :
      ‖((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m t.1 t.2 z‖ ≤ L := by
    obtain ⟨E,hE,hEb⟩ := hb t ht.1 n
    have hbz := hEb m hmn z hz
    have hd : 1 ≤ ‖((n-m:ℤ):ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn.symm)
    have hR : ‖sourcePsiZetaReciprocalTerm hp hp1 φ n m z‖ ≤ K :=
      hbz.1.trans (div_le_self hK hd)
    have hS := hbz.2.trans ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E m).trans hE)
    rw [sourcePsi_zeta_decomposition hp hp1 φ n m t.1 t.2 z]
    have hi : ‖I/(Real.pi:ℂ)‖ = Real.pi⁻¹ := by simp [Real.pi_pos.le,one_div]
    exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
      (by simpa only [hi,L] using add_le_add (add_le_add le_rfl hR) hS)
  let f : (ℤ × ℤ) → ℤ → ℂ := fun j m =>
    if m = j.2 then 0 else ((m-j.2:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 j.1 m j.2 t.1 t.2
  have hpoint (j : ℤ × ℤ) (m : ℤ) : ‖f j m‖ ≤
      Q*(‖t.1 m‖+‖sourcePeriodicMidpointDisplacement hp hp1 t.2 m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 t.2 m‖) := by
    by_cases hmk : m = j.2
    · simp only [f,if_pos hmk,norm_zero]
      positivity
    simp only [f,if_neg hmk]
    by_cases hmn : m = j.1
    · subst m
      rw [sourcePsiOriginalJacobianEntry_deleted_row,mul_zero,norm_zero]
      positivity
    by_cases hkn : j.2 = j.1
    · rw [hkn,sourcePsiOriginalJacobianEntry_deleted_column,mul_zero,norm_zero]
      positivity
    exact H.originalJacobian_offDiagonal_bound hD t.2 (hUV ht.1).2.1 (hUV ht.1).2.2
      hreal j.1 m j.2 hmn hkn hmk t.1 ha L (hZ j.1 m hmn)
  obtain ⟨B,hB,hBn⟩ := Coeff.exists_common_majorant_of_three t.1
    (sourcePeriodicMidpointDisplacement hp hp1 t.2) (sourcePeriodicGapDisplacement hp hp1 t.2) Q hQ f hpoint
  refine ⟨B,hB.trans ?_,?_⟩
  · have ha' : ‖t.1‖ ≤ ‖a₀‖+1 := by
      have hd : ‖t.1-a₀‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using ht.2.1
      have hh := norm_le_norm_sub_add t.1 a₀
      linarith
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add ha' (hm t.2 ht.2.2.1).1) (hg t.2 ht.2.2.2).1) hQ
  · intro n m k hmk
    simpa only [f,if_neg hmk] using hBn (n,k) m

/-- The actual weighted supremum over all off-diagonal columns and equations. -/
def sourcePsiOriginalOffDiagonalRowSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (m : ℤ) : ℝ :=
  sSup ((fun j : ℤ × ℤ =>
    ‖((m-j.2:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 j.1 m j.2 a ψ‖) '' {j | j.2 ≠ m})

theorem SourceLemma12_4Data.originalJacobian_offDiagonal_rowSup
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, IsRealType (CoeffPair.toMax p t.2) →
        t.1 ∈ sourcePsiOriginalRootPlacement D → ∃ B : Coeff p, ‖B‖ ≤ C ∧
          (∀ m : ℤ, B m = (sourcePsiOriginalOffDiagonalRowSup hp hp1 t.1 t.2 m:ℂ)) ∧
          ∀ n m k : ℤ, m ≠ k →
            ‖((m-k:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 n m k t.1 t.2‖ ≤ ‖B m‖ := by
  obtain ⟨U,hU,hbase,hUV,C,hC,hb⟩ :=
    H.originalJacobian_offDiagonal_commonMajorant hW hD hV φ hφW hφV a₀
  refine ⟨U,hU,hbase,hUV,C,hC,?_⟩
  intro t ht hreal ha
  obtain ⟨B,hB,hBn⟩ := hb t ht hreal ha
  obtain ⟨E,hE,hEn,hEB⟩ := NLS.exists_coordinateNormSup (zero_lt_one.trans hp1).ne'
    (fun m => {j : ℤ × ℤ | j.2 ≠ m}) (fun m => ⟨(0,m+1),by simp⟩)
    (fun m j => ((m-j.2:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 j.1 m j.2 t.1 t.2)
    B (fun m j hj => hBn j.1 m j.2 hj.symm)
  exact ⟨E,hEB.trans hB,hE,fun n m k hmk => hEn m (n,k) hmk.symm⟩

end NLS.ZakharovShabat
