import NLS.ZakharovShabat.SourcePsiGlobalTailCoordinateBound

/-!
# A locally uniformly bounded global psi tail sequence

The coordinate estimate on distant selected gaps is dominated by the
root, midpoint, and gap displacement sequences. Local continuity of
the latter two in `ℓᵖ` gives a norm bound independent of the deleted
index and of the complex source in a neighborhood of a real-type base.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Periodic midpoint and gap displacement norms are locally bounded
near an arbitrary real-type source. -/
theorem exists_local_sourcePeriodicDisplacement_normBounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V,
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤
          ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+1 ∧
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤
          ‖sourcePeriodicGapDisplacement hp hp1 φ‖+1 := by
  have hmidCont :=
    continuousAt_sourcePeriodicMidpointDisplacement_of_realType
      hp hp1 φ hφ
  have hgapCont :=
    continuousAt_sourcePeriodicGapDisplacement_of_realType
      hp hp1 φ hφ
  obtain ⟨δm,hδm,hmid⟩ :=
    Metric.continuousAt_iff.mp hmidCont 1 (by norm_num)
  obtain ⟨δg,hδg,hgap⟩ :=
    Metric.continuousAt_iff.mp hgapCont 1 (by norm_num)
  let δ := min δm δg
  have hδ : 0 < δ := lt_min hδm hδg
  refine ⟨ball φ δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro ψ hψ
  have hψm : dist ψ φ < δm :=
    (mem_ball.mp hψ).trans_le (min_le_left _ _)
  have hψg : dist ψ φ < δg :=
    (mem_ball.mp hψ).trans_le (min_le_right _ _)
  have hmidDist : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ-
      sourcePeriodicMidpointDisplacement hp hp1 φ‖ < 1 := by
    simpa only [dist_eq_norm] using hmid hψm
  have hgapDist : ‖sourcePeriodicGapDisplacement hp hp1 ψ-
      sourcePeriodicGapDisplacement hp hp1 φ‖ < 1 := by
    simpa only [dist_eq_norm] using hgap hψg
  constructor
  · have heq : sourcePeriodicMidpointDisplacement hp hp1 ψ =
        sourcePeriodicMidpointDisplacement hp hp1 φ +
          (sourcePeriodicMidpointDisplacement hp hp1 ψ-
            sourcePeriodicMidpointDisplacement hp hp1 φ) := by abel
    have hnorm : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤
        ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ-
            sourcePeriodicMidpointDisplacement hp hp1 φ‖ := by
      calc
        _ = ‖sourcePeriodicMidpointDisplacement hp hp1 φ +
            (sourcePeriodicMidpointDisplacement hp hp1 ψ-
              sourcePeriodicMidpointDisplacement hp hp1 φ)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    linarith
  · have heq : sourcePeriodicGapDisplacement hp hp1 ψ =
        sourcePeriodicGapDisplacement hp hp1 φ +
          (sourcePeriodicGapDisplacement hp hp1 ψ-
            sourcePeriodicGapDisplacement hp hp1 φ) := by abel
    have hnorm : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 φ‖+
          ‖sourcePeriodicGapDisplacement hp hp1 ψ-
            sourcePeriodicGapDisplacement hp hp1 φ‖ := by
      calc
        _ = ‖sourcePeriodicGapDisplacement hp hp1 φ +
            (sourcePeriodicGapDisplacement hp hp1 ψ-
              sourcePeriodicGapDisplacement hp hp1 φ)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    linarith

/-- The distant-selected-index part of the psi equation is a deleted
`ℓᵖ` sequence with one local norm bound uniform in every deleted index. -/
theorem exists_local_sourcePsi_tailEquation_uniformNorm
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a : Coeff p),ψ) ∈ U →
            ∃ F : DeletedCoeff p n,
              (∀ m : ℤ, (F : Coeff p) m =
                if K ≤ m.natAbs then
                  sourcePsiEquationCoordinate hp hp1 n m
                    (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)
                else 0) ∧
              ‖F‖ ≤ C := by
  obtain ⟨Utail,hUtailOpen,hbaseTail,K,Ctail,hCtail,htail⟩ :=
    exists_local_sourcePsi_allDeleted_tailCoordinateBound hp hp1 φ hφ a₀
  obtain ⟨Vnorm,hVnormOpen,hφVnorm,hnorm⟩ :=
    exists_local_sourcePeriodicDisplacement_normBounds hp hp1 φ hφ
  let U : Set (Coeff p × CoeffPair p) :=
    Utail ∩ (ball a₀ 1 ×ˢ Vnorm)
  have hUopen : IsOpen U :=
    hUtailOpen.inter (isOpen_ball.prod hVnormOpen)
  have hbase : (a₀,φ) ∈ U :=
    ⟨hbaseTail,mem_ball_self (by norm_num),hφVnorm⟩
  let T : ℝ := ‖a₀‖+1
  let S : ℝ := ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+
    ‖sourcePeriodicGapDisplacement hp hp1 φ‖+2
  let C₀ : ℝ := 2*Real.pi*Ctail
  let C : ℝ := C₀*(T+S)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC : 0 ≤ C := by dsimp [C,T,S]; positivity
  refine ⟨U,hUopen,hbase,K,C,hC,?_⟩
  intro n a ψ hpair
  obtain ⟨hpairTail,haBall,hψNorm⟩ := hpair
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
  have hAglobal : ‖A‖ ≤ T+S := by
    obtain ⟨hPN,hGN⟩ := hnorm ψ hψNorm
    dsimp [S]
    linarith
  let Fraw : ℤ → ℂ := fun m =>
    if K ≤ m.natAbs then
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
        ((Real.pi : ℂ)*m) (Real.pi/8)
    else 0
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
    by_cases hm : K ≤ m.natAbs
    · have hcoord := htail n a ψ hpairTail m hm
      calc
        ‖Fraw m‖ = (2*Real.pi)*
            ‖(2*(Real.pi:ℂ))⁻¹ * Fraw m‖ := hnormalize _
        _ ≤ (2*Real.pi)*(Ctail*‖A m‖) := by
          gcongr
          simpa only [Fraw,if_pos hm,hAcoord] using hcoord
        _ = C₀*‖A m‖ := by dsimp [C₀]; ring
    · simp only [Fraw,if_neg hm,norm_zero]
      positivity
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
    _ ≤ C₀*(T+S) := mul_le_mul_of_nonneg_left hAglobal hC₀
    _ = C := rfl

end NLS.ZakharovShabat
