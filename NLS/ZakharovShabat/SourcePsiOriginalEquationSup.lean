import NLS.ZakharovShabat.SourceEquation2_26
import NLS.SequenceSpaces.ThreeSequenceMajorant

/-!
# The literal supremum over omitted equations

For a full lp root input, delete coordinate n before evaluating F^n.
One lp majorant bounds every output coordinate for every n. Thus the
printed sequence sup_{n != m}|F_m^n| is itself lp and locally bounded.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePsiFillDeletedRoot_deleteCoordinateTo (n : ℤ) (a : Coeff p) (ξ : ℂ) :
    sourcePsiFillDeletedRoot n (Coeff.deleteCoordinateTo n a) ξ =
      Coeff.deleteCoordinate n a+lp.single p n (ξ-(Real.pi:ℂ)*n) := rfl

theorem SourceCorollary10_6Data.originalEquation_coordinate_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p) (ξ : ℂ) (hξ : ξ ∈ D n) (L : ℝ)
    (hquot : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n (Coeff.deleteCoordinateTo n a) ξ,ψ))‖ ≤ L) :
    ‖(sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n a) ψ:Coeff p) m‖ ≤
      (2*Real.pi*(c*L))*(‖a m‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖) := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψV m d r hr he
  have hb := H.original_coordinate_bound hD ψ hψW hψV n m hmn (Coeff.deleteCoordinateTo n a) ξ hξ d r hr he L hquot
  have hv : ((Coeff.deleteCoordinateTo n a:DeletedCoeff p n):Coeff p) m = a m :=
    Coeff.deleteCoordinate_apply_other n m hmn a
  have hf := H.originalEquation_apply hW ψ hψW n (Coeff.deleteCoordinateTo n a) m P
  change (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n a) ψ:Coeff p) m =
    sourcePsiEquationCoordinate hp hp1 n m ((Coeff.deleteCoordinateTo n a:DeletedCoeff p n):Coeff p) ψ (d:ℂ) r at hf
  rw [← hf,hv] at hb
  let f := (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n a) ψ:Coeff p) m
  have hscale : ‖f‖ = (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹*f‖ := by
    rw [norm_mul,norm_inv,norm_mul]
    simp only [Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  change ‖f‖ ≤ _
  rw [hscale]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*Real.pi)).trans_eq (by ring)

theorem SourceCorollary10_6Data.originalEquation_commonMajorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφW : φ ∈ W) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∃ B : Coeff p, ‖B‖ ≤ C ∧
        ∀ n m : ℤ, ‖(sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2:Coeff p) m‖ ≤ ‖B m‖ := by
  obtain ⟨V,hV,_,hφV,_,D,c,hD'⟩ := H.neighborhoods φ hφW
  have hD : SourceIsolatingNeighborhoods hp hp1 V D c := hD'.toSourceIsolatingNeighborhoods
  let b := sourcePeriodicMidpointDisplacement hp hp1 φ
  obtain ⟨Uq,hUq,hbaseq,L,hL,hquot⟩ := H.local_replaced_allDisk_quotient_errorBound hD hV φ hφW hφV a₀ b
  obtain ⟨_,_,Vm,hVm,hφm,M,hM,hm⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  let U := Uq ∩ (ball a₀ 1 ×ˢ ((W ∩ V) ∩ (Vm ∩ Vg)))
  let Q := 2*Real.pi*(c*(L+1))
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨U,hUq.inter (isOpen_ball.prod ((hW.inter hV).inter (hVm.inter hVg))),
    ⟨hbaseq,mem_ball_self (by norm_num),⟨hφW,hφV⟩,hφm,hφg⟩,
    (fun _ ht => ⟨mem_univ _,ht.2.2.1.1⟩),Q*(‖a₀‖+1+M+G),by positivity,?_⟩
  intro t ht
  obtain ⟨hqt,ha,⟨hψW,hψV⟩,hψm,hψg⟩ := ht
  have hpoint : ∀ n m : ℤ,
      ‖(sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2:Coeff p) m‖ ≤
        Q*(‖t.1 m‖+‖sourcePeriodicMidpointDisplacement hp hp1 t.2 m‖+‖sourcePeriodicGapDisplacement hp hp1 t.2 m‖) := by
    intro n m
    by_cases hmn : m = n
    · subst m
      have hn : (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2:Coeff p) n = 0 :=
        (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2).property
      rw [hn,norm_zero]
      positivity
    obtain ⟨E,hE,_,hEq⟩ := hquot t hqt n
    apply H.originalEquation_coordinate_bound hW hD t.2 hψW hψV n m hmn t.1
      (sourceStandardRootMidpoint hp hp1 φ n)
      (hD.gap φ hφV n (sourcePeriodicMidpoint_mem_segment hp hp1 φ n)) (L+1)
    intro z hz
    rw [sourcePsiFillDeletedRoot_deleteCoordinateTo]
    have herror := (hEq m z hz).trans ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E m).trans hE)
    have hh := norm_le_norm_sub_add (sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(Coeff.deleteCoordinate n t.1+lp.single p n (b n),t.2))) 1
    simpa only [norm_one,b,sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint]
      using hh.trans (add_le_add herror le_rfl)
  obtain ⟨B,hB,hBn⟩ := Coeff.exists_common_majorant_of_three t.1
    (sourcePeriodicMidpointDisplacement hp hp1 t.2) (sourcePeriodicGapDisplacement hp hp1 t.2) Q hQ
    (fun n m => (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2:Coeff p) m) hpoint
  refine ⟨B,hB.trans ?_,hBn⟩
  have ha' : ‖t.1‖ ≤ ‖a₀‖+1 := by
    have hd : ‖t.1-a₀‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using ha
    have hh := norm_le_norm_sub_add t.1 a₀
    linarith
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha' (hm t.2 hψm).1) (hg t.2 hψg).1) hQ

def sourcePsiOriginalEquationIndexSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (m : ℤ) : ℝ :=
  sSup ((fun n => ‖(sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n a) ψ:Coeff p) m‖) '' {n : ℤ | n ≠ m})

/-- The actual supremum over every omitted equation is an lp sequence,
locally bounded on the original full-input topology. -/
theorem SourceLemma12_4Data.originalEquation_indexSup
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∃ B : Coeff p, ‖B‖ ≤ C ∧
        (∀ m : ℤ, B m = (sourcePsiOriginalEquationIndexSup hp hp1 t.1 t.2 m : ℂ)) ∧
        ∀ n m : ℤ, m ≠ n →
          ‖(sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2:Coeff p) m‖ ≤ ‖B m‖ := by
  obtain ⟨U,hU,hbase,hUW,C,hC,hb⟩ := H.previous.quotients.originalEquation_commonMajorant hW φ hφ a₀
  refine ⟨U,hU,hbase,hUW,C,hC,?_⟩
  intro t ht
  obtain ⟨B,hB,hpoint⟩ := hb t ht
  obtain ⟨E,hE,hEpoint,hEn⟩ := NLS.exists_coordinateNormSup (zero_lt_one.trans hp1).ne'
    (fun m => {n : ℤ | n ≠ m}) (fun m => ⟨m+1,by simp⟩)
    (fun m n => (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2:Coeff p) m)
    B (fun m n _ => hpoint n m)
  exact ⟨E,hEn.trans hB,hE,fun n m hmn => hEpoint m n hmn.symm⟩

end NLS.ZakharovShabat
