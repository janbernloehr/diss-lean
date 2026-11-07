import NLS.ZakharovShabat.SourceL2UnitFundamentalSymmetries
import NLS.ZakharovShabat.L2WholeLineDiscriminantGradient

/-! # Actual pointwise gradient and xi symmetries on the entire real line

Original complex L2 sources are included. The unit-period proof uses the
actual normalized fundamental matrix. Periodicity extends the polynomial
identities through all positive and negative periods and every seam.
-/
noncomputable section
open Set Complex Matrix
namespace NLS.ZakharovShabat

private theorem whole_matrix_on_unit (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2WholeLineFundamentalMatrix u z t = l2FundamentalMatrix u z t := by
  simpa only [Int.cast_zero,zero_add,sub_zero,_root_.zpow_zero,Units.val_one,Matrix.mul_one]
    using l2WholeLineFundamentalMatrix_on_period u z 0 t (by simpa only [Int.cast_zero,zero_add] using t.property)

private theorem periodic_eq_of_unit {E : Type} (f g : ℝ → E)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hu : ∀ t : Icc (0:ℝ) 1, f t = g t) : f = g := by
  funext x
  let n : ℤ := ⌊x⌋
  have ht : x-(n:ℝ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · linarith [Int.floor_le x]
    · linarith [Int.lt_floor_add_one x]
  have he := hu ⟨x-n,ht⟩
  have hfx := hf.sub_int_mul_eq (x := x) n
  have hgx := hg.sub_int_mul_eq (x := x) n
  simp only [mul_one] at hfx hgx
  exact hfx.symm.trans (he.trans hgx)

theorem l2WholeLineDiscriminantGradient_sourceComponentSwap (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) x =
      (l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x).swap := by
  apply congrFun (periodic_eq_of_unit _ _
    (periodic_l2WholeLineDiscriminantGradient _ _)
    (fun y => congrArg Prod.swap (periodic_l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z y)) _) x
  intro t
  unfold l2WholeLineDiscriminantGradient
  rw [whole_matrix_on_unit,whole_matrix_on_unit,l2FundamentalMatrix_sourceComponentSwap,
    l2Monodromy_sourceComponentSwap]
  exact discriminantGradientMatrix_componentSwap _ _

theorem l2WholeLineDiscriminantXi_sourceComponentSwap (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) x =
      -l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x := by
  apply congrFun (periodic_eq_of_unit _ _ (periodic_l2WholeLineDiscriminantXi _ _)
    (fun y => congrArg Neg.neg (periodic_l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z y)) _) x
  intro t
  unfold l2WholeLineDiscriminantXi
  rw [whole_matrix_on_unit,whole_matrix_on_unit,l2FundamentalMatrix_sourceComponentSwap,
    l2Monodromy_sourceComponentSwap]
  exact discriminantXiMatrix_componentSwap _ _

theorem l2WholeLineDiscriminantGradient_sourceReciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z x =
      (c⁻¹*(l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x).1,
       c*(l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x).2) := by
  have hp : Function.Periodic (fun y =>
      (c⁻¹*(l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z y).1,
       c*(l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z y).2)) 1 := by
    intro y
    dsimp only
    rw [periodic_l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z y]
  apply congrFun (periodic_eq_of_unit _ _ (periodic_l2WholeLineDiscriminantGradient _ _) hp _) x
  intro t
  unfold l2WholeLineDiscriminantGradient
  rw [whole_matrix_on_unit,whole_matrix_on_unit,l2FundamentalMatrix_sourceReciprocalScaling c hc,
    l2Monodromy_sourceReciprocalScaling c hc]
  exact discriminantGradientMatrix_reciprocalScaling c hc _ _

theorem l2WholeLineDiscriminantXi_sourceReciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z x =
      l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x := by
  apply congrFun (periodic_eq_of_unit _ _ (periodic_l2WholeLineDiscriminantXi _ _)
    (periodic_l2WholeLineDiscriminantXi _ _) _) x
  intro t
  unfold l2WholeLineDiscriminantXi
  rw [whole_matrix_on_unit,whole_matrix_on_unit,l2FundamentalMatrix_sourceReciprocalScaling c hc,
    l2Monodromy_sourceReciprocalScaling c hc]
  exact discriminantXiMatrix_reciprocalScaling c hc _ _

theorem l2WholeLineDiscriminantGradient_sourceSpatialReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceSpatialReflection φ)) z x =
      (l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z (1-x)).swap := by
  have hp : Function.Periodic (fun y => (l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z (1-y)).swap) 1 := by
    intro y
    dsimp only
    rw [show 1-(y+1)=1-y-1 by ring,
      (periodic_l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z).sub_eq (1-y)]
  apply congrFun (periodic_eq_of_unit _ _ (periodic_l2WholeLineDiscriminantGradient _ _) hp _) x
  intro t
  let s : Icc (0:ℝ) 1 := ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
  change l2WholeLineDiscriminantGradient _ _ t = (l2WholeLineDiscriminantGradient _ _ s).swap
  unfold l2WholeLineDiscriminantGradient
  rw [whole_matrix_on_unit,whole_matrix_on_unit,l2FundamentalMatrix_sourceSpatialReflection,
    l2Monodromy_sourceSpatialReflection]
  have h := discriminantGradientMatrix_spatialReflection (l2Monodromy (sourcePhysicalL2 φ) z)
    (l2FundamentalMatrix (sourcePhysicalL2 φ) z s)
  simpa only [det_l2Monodromy,one_smul,spatialReflectionMonodromyMatrix,s] using h

theorem l2WholeLineDiscriminantXi_sourceSpatialReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceSpatialReflection φ)) z x =
      l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z (1-x) := by
  have hp : Function.Periodic (fun y => l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z (1-y)) 1 := by
    intro y
    dsimp only
    rw [show 1-(y+1)=1-y-1 by ring,
      (periodic_l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z).sub_eq (1-y)]
  apply congrFun (periodic_eq_of_unit _ _ (periodic_l2WholeLineDiscriminantXi _ _) hp _) x
  intro t
  let s : Icc (0:ℝ) 1 := ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
  change l2WholeLineDiscriminantXi _ _ t = l2WholeLineDiscriminantXi _ _ s
  unfold l2WholeLineDiscriminantXi
  rw [whole_matrix_on_unit,whole_matrix_on_unit,l2FundamentalMatrix_sourceSpatialReflection,
    l2Monodromy_sourceSpatialReflection]
  have h := discriminantXiMatrix_spatialReflection (l2Monodromy (sourcePhysicalL2 φ) z)
    (l2FundamentalMatrix (sourcePhysicalL2 φ) z s)
  simpa only [det_l2Monodromy,one_mul,spatialReflectionMonodromyMatrix,s] using h

theorem l2WholeLineDiscriminantGradient_sourceMidpointReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) x =
      l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z (1-x) := by
  change l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceComponentSwap (sourceSpatialReflection φ))) (-z) x = _
  rw [l2WholeLineDiscriminantGradient_sourceComponentSwap,l2WholeLineDiscriminantGradient_sourceSpatialReflection,
    Prod.swap_swap]

theorem l2WholeLineDiscriminantXi_sourceMidpointReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) x =
      -l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z (1-x) := by
  change l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceComponentSwap (sourceSpatialReflection φ))) (-z) x = _
  rw [l2WholeLineDiscriminantXi_sourceComponentSwap,l2WholeLineDiscriminantXi_sourceSpatialReflection]

end NLS.ZakharovShabat
