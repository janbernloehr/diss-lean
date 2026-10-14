import NLS.ZakharovShabat.SourcePsiOriginalCoordinateBound
import NLS.SequenceSpaces.SandwichMajorant

/-!
# The literal psi equation is locally bounded in lp on the original domain

One neighborhood works for every deleted index and every nearby arbitrary
root input. The source point may be complex. The original isolating disks
are retained, and the output coordinates are exactly the contour formula.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePsi_equation_sequence_of_coordinate_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (d : ℤ → ℝ) (r : ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ m : ℤ, m ≠ n →
      ‖(2*(Real.pi:ℂ))⁻¹*sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d m:ℂ) (r m)‖ ≤
        (‖(a:Coeff p) m‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖)*C) :
    ∃ F : DeletedCoeff p n,
      (∀ m : ℤ, (F:Coeff p) m = sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d m:ℂ) (r m)) ∧
      ‖F‖ ≤ (2*Real.pi*C)*(‖a‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖) := by
  let A : Coeff p := Coeff.magnitude (a:Coeff p)+
    Coeff.magnitude (sourcePeriodicMidpointDisplacement hp hp1 ψ)+
    Coeff.magnitude (sourcePeriodicGapDisplacement hp hp1 ψ)
  have hAn (m : ℤ) : ‖A m‖ = ‖(a:Coeff p) m‖+
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hA : ‖A‖ ≤ ‖a‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+
      ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ := by
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans_eq (by
      simp only [Coeff.norm_magnitude]; rfl))
  let raw : ℤ → ℂ := fun m => sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d m:ℂ) (r m)
  let B : Coeff p := ((2*Real.pi*C:ℝ):ℂ) • A
  have hBn (m : ℤ) : ‖B m‖ = (2*Real.pi*C)*‖A m‖ := by
    simp only [B,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi*C)]
  have hraw (m : ℤ) : ‖raw m‖ ≤ ‖B m‖ := by
    rw [hBn,hAn]
    by_cases hmn : m = n
    · subst m
      simp only [raw,sourcePsiEquationCoordinate,sub_self,Int.cast_zero,zero_mul,norm_zero]
      positivity
    · have hb := hbound m hmn
      have hscale : ‖raw m‖ = (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹*raw m‖ := by
        rw [norm_mul,norm_inv,norm_mul]
        simp only [Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
        field_simp
      rw [hscale]
      calc
        _ ≤ (2*Real.pi)*((‖(a:Coeff p) m‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖)*C) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by ring
  let F₀ : Coeff p := ⟨raw,(lp.memℓp B).mono' hraw⟩
  have hn : F₀ n = 0 := by simp [F₀,raw,sourcePsiEquationCoordinate]
  refine ⟨⟨F₀,hn⟩,fun _ => rfl,?_⟩
  change ‖F₀‖ ≤ _
  calc
    ‖F₀‖ ≤ ‖B‖ := lp.norm_mono (zero_lt_one.trans hp1).ne' hraw
    _ = (2*Real.pi*C)*‖A‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

/-- On every supplied original isolating family, the actual equation
sequences have a common local norm bound at every complex source in W. -/
theorem SourceCorollary10_6Data.original_equation_uniformNorm
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ d r : ℤ → ℝ, (∀ m : ℤ, 0 < r m ∧ D m = ball (d m:ℂ) (r m)) ∧
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a:Coeff p),ψ) ∈ U → ∃ F : DeletedCoeff p n,
            (∀ m : ℤ, (F:Coeff p) m = sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d m:ℂ) (r m)) ∧
            ‖F‖ ≤ C := by
  choose d r hr he using hD.discs
  obtain ⟨Uq,hUq,hbaseq,Q,hQ,hquot⟩ := H.local_filled_allDisk_quotient_bound hD hV φ hφW hφV
    a₀ (sourcePeriodicMidpointDisplacement hp hp1 φ)
  obtain ⟨_,_,Vm,hVm,hφm,M,hM,hm⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  let U := Uq ∩ (ball a₀ 1 ×ˢ ((W ∩ V) ∩ (Vm ∩ Vg)))
  let C := (2*Real.pi*(c*Q))*(‖a₀‖+1+M+G)
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  refine ⟨d,r,fun m => ⟨hr m,he m⟩,U,
    hUq.inter (isOpen_ball.prod ((hW.inter hV).inter (hVm.inter hVg))),
    ⟨hbaseq,mem_ball_self (by norm_num),⟨hφW,hφV⟩,hφm,hφg⟩,
    (fun _ ht => ⟨mem_univ _,ht.2.2.1⟩),C,by dsimp [C]; positivity,?_⟩
  intro n a ψ ht
  obtain ⟨hq,ha,⟨hψW,hψV⟩,hψm,hψg⟩ := ht
  obtain ⟨F,hF,hFnorm⟩ := sourcePsi_equation_sequence_of_coordinate_bound hp hp1 n a ψ d r (c*Q)
    (mul_nonneg hc hQ) (by
      intro m hmn
      apply H.original_coordinate_bound hD ψ hψW hψV n m hmn a
        (sourceStandardRootMidpoint hp hp1 φ n)
        (hD.gap φ hφV n (sourcePeriodicMidpoint_mem_segment hp hp1 φ n)) (d m) (r m) (hr m) (he m) Q
      intro z hz
      simpa only [sourcePsiFillDeletedRoot,sourceStandardRootMidpoint,sourcePeriodicMidpointDisplacement_apply]
        using hquot ((a:Coeff p),ψ) hq n m z hz)
  refine ⟨F,hF,hFnorm.trans ?_⟩
  have han : ‖a‖ ≤ ‖a₀‖+1 := by
    have hd : ‖(a:Coeff p)-a₀‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using ha
    have hh := norm_le_norm_sub_add (a:Coeff p) a₀
    change ‖(a:Coeff p)‖ ≤ _
    linarith
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add han (hm ψ hψm).1) (hg ψ hψg).1)
    (by positivity)

end NLS.ZakharovShabat
