import NLS.ZakharovShabat.SourcePsiGapFactorization
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-!
# Disc majorants for arbitrary psi root displacements

The regular product in the psi gap factorization is the single-root
quotient from Lemma 10.8. Its displacement from the periodic midpoint
is an actual `ℓᵖ` sequence for every psi root parameter. The existing
quotient estimates therefore apply without assuming the psi roots have
already been solved by the implicit-function theorem.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The offset required by Lemma 10.8 is the difference of two
`ℓᵖ` displacement sequences. -/
theorem sourcePsi_midpoint_offset_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (m : ℤ) :
    displacedRoots a m -
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m =
      (a - sourcePeriodicMidpointDisplacement hp hp1 ψ) m := by
  simp only [displacedRoots, lp.coeFn_sub, Pi.sub_apply,
    sourcePeriodicMidpointDisplacement_apply]
  ring

/-- On one source neighborhood, every psi root sequence has
`ℓᵖ + ℓ^(p/2)` majorants for the regular quotient error on all
sufficiently distant selected discs. -/
theorem exists_local_sourcePsiQuotient_discMajorants
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ K : ℕ, ∀ ψ ∈ V, ∀ a : Coeff p,
          ∃ Bp : Coeff p,
          ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
            ∀ m : ℤ, K ≤ m.natAbs →
              ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
                ‖sourceSingleRootQuotientJointProduct hp hp1 m
                  (z,(a,ψ))-1‖ ≤ ‖Bp m‖+‖Bg m‖ := by
  obtain ⟨N,ε,hε,_,V,hVopen,_,hφV,C,R,H,hC,hR,hH,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data hp hp1 φ hφ
  refine ⟨N,ε,hε,V,hVopen,hφV,max (N+1) K,?_⟩
  intro ψ hψ a
  let α : Coeff p := a - sourcePeriodicMidpointDisplacement hp hp1 ψ
  have hα (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m :=
    sourcePsi_midpoint_offset_apply hp hp1 a ψ m
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ
  obtain ⟨Bp,Bg,hpoint,_,_⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants
      hp hp1 hp1 hp φ ψ a α hα N K ε C R hC hR
      hdisp hsep (hdom a) hsmall
  exact ⟨Bp,Bg,hpoint⟩

/-- The two quotient error majorants combine into one `ℓᵖ`
majorant, including when `p/2 < 1`. -/
theorem exists_local_sourcePsiQuotient_lpDiscMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ K : ℕ, ∀ ψ ∈ V, ∀ a : Coeff p,
          ∃ B : Coeff p,
            ∀ m : ℤ, K ≤ m.natAbs →
              ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
                ‖sourceSingleRootQuotientJointProduct hp hp1 m
                  (z,(a,ψ))-1‖ ≤ ‖B m‖ := by
  obtain ⟨N,ε,hε,V,hVopen,hφV,K,hmajor⟩ :=
    exists_local_sourcePsiQuotient_discMajorants hp hp1 φ hφ
  refine ⟨N,ε,hε,V,hVopen,hφV,K,?_⟩
  intro ψ hψ a
  obtain ⟨Bp,Bg,hpoint⟩ := hmajor ψ hψ a
  let r := ENNReal.ofReal (p.toReal/2)
  have hr : 0 < r := ENNReal.ofReal_pos.mpr (by
    have hpr : 0 < p.toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
    positivity)
  have hrp : r ≤ p := by
    calc
      r ≤ ENNReal.ofReal p.toReal := by
        dsimp [r]
        apply ENNReal.ofReal_le_ofReal
        have hpr : 0 ≤ p.toReal := ENNReal.toReal_nonneg
        linarith
      _ = p := ENNReal.ofReal_toReal hp
  let BgP : Coeff p := ⟨fun m => Bg m,(lp.memℓp Bg).of_exponent_ge hrp⟩
  let B : Coeff p := Coeff.magnitude Bp + Coeff.magnitude BgP
  refine ⟨B,?_⟩
  intro m hm z hz
  have hBpoint : ‖B m‖ = ‖Bp m‖+‖Bg m‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply]
    rw [← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [hBpoint]
  exact hpoint m hm z hz

end NLS.ZakharovShabat
