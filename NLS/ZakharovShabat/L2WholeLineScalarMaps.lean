import NLS.ZakharovShabat.L2WholeLineWeakDerivative

/-! # Scalar coordinate maps for the original whole-line Hermitian L2 space -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.ZakharovShabat

abbrev WholeLineScalarL2 := Lp ℂ 2 (volume : Measure ℝ)

def wholeLineFirstCoordinate : WholeLineL2 →L[ℂ] WholeLineScalarL2 :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).toContinuousLinearMap).compLpL 2 volume

def wholeLineSecondCoordinate : WholeLineL2 →L[ℂ] WholeLineScalarL2 :=
  ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).toContinuousLinearMap).compLpL 2 volume

def wholeLineFirstEmbedding : WholeLineScalarL2 →L[ℂ] WholeLineL2 :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ ℂ).prod 0)).compLpL 2 volume

def wholeLineSecondEmbedding : WholeLineScalarL2 →L[ℂ] WholeLineL2 :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.comp
    ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))).compLpL 2 volume

theorem wholeLineFirstCoordinate_ae (f : WholeLineL2) :
    wholeLineFirstCoordinate f =ᵐ[volume] (fun t => (wholeLineL2Pair f t).1) :=
  ContinuousLinearMap.coeFn_compLpL _ f

theorem wholeLineSecondCoordinate_ae (f : WholeLineL2) :
    wholeLineSecondCoordinate f =ᵐ[volume] (fun t => (wholeLineL2Pair f t).2) :=
  ContinuousLinearMap.coeFn_compLpL _ f

theorem wholeLineFirstEmbedding_pair_ae (f : WholeLineScalarL2) :
    wholeLineL2Pair (wholeLineFirstEmbedding f) =ᵐ[volume] (fun t => (f t,0)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℂ ℂ).prod 0)) f] with t ht
  exact congrArg WithLp.ofLp ht

theorem wholeLineSecondEmbedding_pair_ae (f : WholeLineScalarL2) :
    wholeLineL2Pair (wholeLineSecondEmbedding f) =ᵐ[volume] (fun t => (0,f t)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.comp
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))) f] with t ht
  exact congrArg WithLp.ofLp ht

/-- The scalar coordinates recover the actual original whole-line L2 vector. -/
theorem wholeLine_embeddings_coordinates (f : WholeLineL2) :
    wholeLineFirstEmbedding (wholeLineFirstCoordinate f) +
      wholeLineSecondEmbedding (wholeLineSecondCoordinate f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (wholeLineFirstEmbedding (wholeLineFirstCoordinate f))
    (wholeLineSecondEmbedding (wholeLineSecondCoordinate f)),
    wholeLineFirstEmbedding_pair_ae (wholeLineFirstCoordinate f),
    wholeLineSecondEmbedding_pair_ae (wholeLineSecondCoordinate f),
    wholeLineFirstCoordinate_ae f,wholeLineSecondCoordinate_ae f] with t hadd h1 h2 hf1 hf2
  rw [hadd]
  apply (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).injective
  change wholeLineL2Pair (wholeLineFirstEmbedding (wholeLineFirstCoordinate f)) t +
    wholeLineL2Pair (wholeLineSecondEmbedding (wholeLineSecondCoordinate f)) t = wholeLineL2Pair f t
  rw [h1,h2,hf1,hf2]
  simp

end NLS.ZakharovShabat
