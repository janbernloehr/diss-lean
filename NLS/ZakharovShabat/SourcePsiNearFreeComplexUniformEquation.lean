import NLS.ZakharovShabat.SourcePsiNearFreeComplexCoordinate
import NLS.ZakharovShabat.SourcePsiNearFreeUniformEquation

/-!
# A locally uniform complex-source psi equation

The quadratic complex-gap correction is absorbed by the periodic-gap
displacement sequence. This turns the coordinate estimate into a
deleted `ℓᵖ` equation with a bound uniform in the deleted index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The complex-gap correction can be absorbed by the same three
`ℓᵖ` displacements that control the real-type equation. -/
theorem nearFree_complex_deletedPsi_normalizedCoordinate_bound_uniform
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (hgeom : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (B : Coeff p)
    (hB : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖(((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (a : Coeff p) ψ z)‖ ≤
        (2/Real.pi)*(1+‖B m‖))
    (T : ℝ) (ha : ‖(a : Coeff p) m‖ ≤ T) :
    let K : ℝ := (Real.pi/8)*(T+Real.pi/8)*(Real.pi/32) /
      (2*(Real.pi/16)^3)
    ‖(2*(Real.pi:ℂ))⁻¹ *
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
        ((Real.pi : ℂ)*m) (Real.pi/8)‖ ≤
      (1+K)*
        (‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖) *
        ((2/Real.pi)*(1+‖B m‖)) := by
  let G := sourcePeriodicGapDisplacement hp hp1 ψ m
  let P := sourcePeriodicMidpointDisplacement hp hp1 ψ m
  let σ := displacedRoots (a : Coeff p) m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let c : ℂ := (Real.pi : ℂ)*m
  let L : ℝ := (2/Real.pi)*(1+‖B m‖)
  let K : ℝ := (Real.pi/8)*(T+Real.pi/8)*(Real.pi/32) /
    (2*(Real.pi/16)^3)
  dsimp only
  have hT : 0 ≤ T := (norm_nonneg _).trans ha
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hσ : ‖σ-c‖ ≤ T := by
    have heq : σ-c = (a : Coeff p) m := by
      simp [σ,c,displacedRoots]
    rw [heq]
    exact ha
  have hτ : ‖τ-σ‖ ≤ ‖(a : Coeff p) m‖+‖P‖ := by
    have hoff := sourcePsi_midpoint_offset_apply
      hp hp1 (a : Coeff p) ψ m
    change σ-τ = ((a : Coeff p)-sourcePeriodicMidpointDisplacement
      hp hp1 ψ) m at hoff
    rw [show τ-σ = -(σ-τ) by ring,norm_neg,hoff]
    simpa only [lp.coeFn_sub,Pi.sub_apply] using
      norm_sub_le ((a : Coeff p) m) P
  have hg2 : ‖G‖^2 ≤ (Real.pi/32)*‖G‖ := by
    nlinarith [mul_nonneg (norm_nonneg G)
      (sub_nonneg.mpr hgap)]
  have hcoord := nearFree_complex_deletedPsi_normalizedCoordinate_bound
    hp hp1 ψ n m hmn a W hψW hQ hgeom hcircle hmid hgap B hB
  have hcorr : (Real.pi/8)*(‖σ-c‖+Real.pi/8)*L*
      (‖G‖^2/(2*(Real.pi/16)^3)) ≤ K*‖G‖*L := by
    calc
      (Real.pi/8)*(‖σ-c‖+Real.pi/8)*L*
          (‖G‖^2/(2*(Real.pi/16)^3)) ≤
        (Real.pi/8)*(T+Real.pi/8)*L*
          (((Real.pi/32)*‖G‖)/(2*(Real.pi/16)^3)) := by
            gcongr
      _ = K*‖G‖*L := by dsimp [K]; ring
  have hbase : ‖τ-σ‖*L ≤
      (‖(a : Coeff p) m‖+‖P‖)*L :=
    mul_le_mul_of_nonneg_right hτ hL
  have hA : ‖τ-σ‖*L + K*‖G‖*L ≤
      (1+K)*(‖(a : Coeff p) m‖+‖P‖+‖G‖)*L := by
    have hx : ‖(a : Coeff p) m‖+‖P‖ ≥ 0 := by positivity
    calc
      ‖τ-σ‖*L + K*‖G‖*L ≤
          (‖(a : Coeff p) m‖+‖P‖)*L + K*‖G‖*L :=
        add_le_add hbase le_rfl
      _ = (‖(a : Coeff p) m‖+‖P‖+K*‖G‖)*L := by ring
      _ ≤ ((1+K)*(‖(a : Coeff p) m‖+‖P‖+‖G‖))*L := by
        apply mul_le_mul_of_nonneg_right _ hL
        nlinarith [mul_nonneg hK hx, norm_nonneg G]
      _ = _ := by ring
  calc
    ‖(2*(Real.pi:ℂ))⁻¹ *
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
          c (Real.pi/8)‖ ≤
      ‖τ-σ‖*L + (Real.pi/8)*(‖σ-c‖+Real.pi/8)*L*
        (‖G‖^2/(2*(Real.pi/16)^3)) := hcoord
    _ ≤ ‖τ-σ‖*L + K*‖G‖*L := add_le_add le_rfl hcorr
    _ ≤ _ := hA

/-- Near every root input over the free source, the complex-source psi
contour equation is a deleted `ℓᵖ` sequence with a locally uniform
norm bound, independent of the deleted index. -/
theorem exists_nearFree_complex_deletedPsi_equation_uniformNorm
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a : Coeff p),ψ) ∈ U →
            ∃ F : DeletedCoeff p n,
              (∀ m : ℤ, (F : Coeff p) m =
                sourcePsiEquationCoordinate hp hp1 n m
                  (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)) ∧
              ‖F‖ ≤ C := by
  obtain ⟨Ureg,hUregOpen,hbaseReg,M,hM,hreg⟩ :=
    exists_nearFree_deletedPsi_uniformRegularFactorMajorant hp hp1 a₀
  obtain ⟨Vsmall,hVsmallOpen,hzeroSmall,hsmall⟩ :=
    exists_nearFree_allPeriodicMidpointGap_small hp hp1
  obtain ⟨Vgeom,hVgeomOpen,hzeroGeom,hgeom⟩ :=
    exists_nearFree_freeQuarterDisc_subset_omittedDomain hp hp1
  obtain ⟨Vcircle,hVcircleOpen,hzeroCircle,hcircle⟩ :=
    exists_nearFree_freeEighthCircle_subset_rootDomain hp hp1
  obtain ⟨Vnorm,hVnormOpen,hzeroNorm,hnorm⟩ :=
    exists_nearFree_sourcePeriodicDisplacement_norms_le_one hp hp1
  obtain ⟨W,hWopen,_,hrealW,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hrealW (by simp [realTypeSourceLocus])
  let V := Vsmall ∩ Vgeom ∩ Vcircle ∩ Vnorm ∩ W
  have hVopen : IsOpen V :=
    ((((hVsmallOpen.inter hVgeomOpen).inter hVcircleOpen).inter
      hVnormOpen).inter hWopen)
  have hzeroV : (0 : CoeffPair p) ∈ V :=
    ⟨⟨⟨⟨hzeroSmall,hzeroGeom⟩,hzeroCircle⟩,hzeroNorm⟩,hzeroW⟩
  let U : Set (Coeff p × CoeffPair p) :=
    Ureg ∩ (ball a₀ 1 ×ˢ V)
  have hUopen : IsOpen U := hUregOpen.inter (isOpen_ball.prod hVopen)
  have hbase : (a₀,(0 : CoeffPair p)) ∈ U :=
    ⟨hbaseReg,mem_ball_self (by norm_num),hzeroV⟩
  let T : ℝ := ‖a₀‖+1
  let K : ℝ := (Real.pi/8)*(T+Real.pi/8)*(Real.pi/32) /
    (2*(Real.pi/16)^3)
  let C₀ : ℝ := 4*(1+M)*(1+K)
  let C : ℝ := C₀*(T+2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC : 0 ≤ C := by dsimp [C,T]; positivity
  refine ⟨U,hUopen,hbase,C,hC,?_⟩
  intro n a ψ hpair
  obtain ⟨hpairReg,haBall,hψV⟩ := hpair
  obtain ⟨⟨⟨⟨hψsmall,hψgeom⟩,hψcircle⟩,hψnorm⟩,hψW⟩ := hψV
  obtain ⟨B,hBnorm,hB⟩ := hreg n a ψ hpairReg
  let P := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  let A : Coeff p := Coeff.magnitude (a : Coeff p) +
    Coeff.magnitude P + Coeff.magnitude G
  have hAcoord (m : ℤ) : ‖A m‖ =
      ‖(a : Coeff p) m‖+‖P m‖+‖G m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
      ← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hAnorm : ‖A‖ ≤ ‖(a : Coeff p)‖+‖P‖+‖G‖ := by
    calc
      ‖A‖ ≤ ‖Coeff.magnitude (a : Coeff p)‖+
          ‖Coeff.magnitude P‖+‖Coeff.magnitude G‖ := by
        dsimp [A]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [Coeff.norm_magnitude]
  have ha : ‖(a : Coeff p)‖ ≤ T := by
    have hdist : ‖(a : Coeff p)-a₀‖ < 1 := by
      simpa only [mem_ball,dist_eq_norm] using haBall
    have hsum : ‖(a : Coeff p)‖ ≤ ‖a₀‖+‖(a : Coeff p)-a₀‖ := by
      have heq : (a : Coeff p) = a₀+((a : Coeff p)-a₀) := by abel
      calc
        ‖(a : Coeff p)‖ = ‖a₀+((a : Coeff p)-a₀)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    dsimp [T]
    linarith
  have hAglobal : ‖A‖ ≤ T+2 := by
    have hPN := (hnorm ψ hψnorm).1
    have hGN := (hnorm ψ hψnorm).2
    linarith
  let Fraw : ℤ → ℂ := fun m =>
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      ((Real.pi : ℂ)*m) (Real.pi/8)
  have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hnormalize (X : ℂ) : ‖X‖ =
      (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹ * X‖ := by
    have heq : (2*(Real.pi:ℂ)) *
        ((2*(Real.pi:ℂ))⁻¹*X) = X := by
      rw [← mul_assoc,mul_inv_cancel₀ hπ,one_mul]
    calc
      ‖X‖ = ‖(2*(Real.pi:ℂ)) *
          ((2*(Real.pi:ℂ))⁻¹*X)‖ := congrArg norm heq.symm
      _ = _ := by
        rw [norm_mul]
        simp [Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
  have hpoint (m : ℤ) : ‖Fraw m‖ ≤ C₀*‖A m‖ := by
    by_cases hmn : m = n
    · subst m
      simp [Fraw,sourcePsiEquationCoordinate]
      positivity
    have hacoord : ‖(a : Coeff p) m‖ ≤ T :=
      (lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) (a : Coeff p) m).trans ha
    have hcoord :=
      nearFree_complex_deletedPsi_normalizedCoordinate_bound_uniform
        hp hp1 ψ n m hmn a W hψW (hQ m).2
        ((Metric.closedBall_subset_closedBall
          (by nlinarith [Real.pi_pos])).trans (hgeom ψ hψgeom m))
        (hcircle ψ hψcircle m)
        (hsmall ψ hψsmall m).1 (hsmall ψ hψsmall m).2
        B (hB m hmn) T hacoord
    have hBcoord : ‖B m‖ ≤ M :=
      (lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m).trans hBnorm
    calc
      ‖Fraw m‖ = (2*Real.pi)*
          ‖(2*(Real.pi:ℂ))⁻¹ * Fraw m‖ := hnormalize _
      _ ≤ (2*Real.pi)*
          ((1+K)*‖A m‖*((2/Real.pi)*(1+‖B m‖))) := by
        gcongr
        simpa only [Fraw,hAcoord] using hcoord
      _ ≤ (2*Real.pi)*
          ((1+K)*‖A m‖*((2/Real.pi)*(1+M))) := by
        gcongr
      _ = C₀*‖A m‖ := by
        dsimp [C₀]
        field_simp [Real.pi_ne_zero]
        ring
  let D : Coeff p := (C₀ : ℂ) • A
  have hDcoord (m : ℤ) : ‖D m‖ = C₀*‖A m‖ := by
    simp only [D,lp.coeFn_smul,Pi.smul_apply,norm_smul,
      Complex.norm_real,Real.norm_of_nonneg hC₀]
  have hmajor : Memℓp (fun m : ℤ => C₀*‖A m‖) p :=
    (lp.memℓp A).norm.const_mul C₀
  have hmem : Memℓp Fraw p := by
    apply hmajor.mono
    intro m
    exact hpoint m
  let Fcoeff : Coeff p := ⟨Fraw,hmem⟩
  have hFn : Fcoeff n = 0 := by
    simp [Fcoeff,Fraw,sourcePsiEquationCoordinate]
  let F : DeletedCoeff p n := ⟨Fcoeff,hFn⟩
  refine ⟨F,fun _ => rfl,?_⟩
  have hFle : ‖Fcoeff‖ ≤ ‖D‖ := by
    apply lp.norm_mono (zero_lt_one.trans hp1).ne'
    intro m
    rw [hDcoord]
    exact hpoint m
  have hDnorm : ‖D‖ = C₀*‖A‖ := by
    simp only [D,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC₀]
  change ‖Fcoeff‖ ≤ C
  calc
    ‖Fcoeff‖ ≤ ‖D‖ := hFle
    _ = C₀*‖A‖ := hDnorm
    _ ≤ C₀*(T+2) := mul_le_mul_of_nonneg_left hAglobal hC₀
    _ = C := rfl

end NLS.ZakharovShabat
