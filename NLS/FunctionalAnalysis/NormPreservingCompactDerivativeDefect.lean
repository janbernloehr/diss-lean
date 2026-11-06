import NLS.FunctionalAnalysis.SecondDerivativePostcomposition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- Differentiating the exact norm trace twice identifies the entire
scalar Hessian defect of the actual derivative, on every pair of directions. -/
theorem secondDerivative_pairing_of_norm_map
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : E → Y) (hF : AnalyticOnNhd ℝ F univ) (hn : ∀ p, ‖F p‖ = ‖p‖)
    (q k h : E) :
    (fderiv ℝ (fderiv ℝ (fun p => inner ℝ (F q) (F p))) q) k h =
      inner ℝ k h-inner ℝ (fderiv ℝ F q k) (fderiv ℝ F q h) := by
  have hfirst (p v : E) : inner ℝ (F p) (fderiv ℝ F p v) = inner ℝ p v := by
    have hd := (hF p (mem_univ _)).differentiableAt.hasFDerivAt.norm_sq
    have he : (fun p => ‖F p‖^2) = (fun p : E => ‖p‖^2) := funext (fun p => by rw [hn p])
    rw [he] at hd
    have hu := hd.unique (hasStrictFDerivAt_norm_sq p).hasFDerivAt
    have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hu
    simp only [two_smul,add_apply,ContinuousLinearMap.comp_apply] at hv
    change inner ℝ (F p) (fderiv ℝ F p v)+inner ℝ (F p) (fderiv ℝ F p v) =
      inner ℝ p v+inner ℝ p v at hv
    linarith
  have hq := hF q (mem_univ _)
  have hh := hq.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const h q)
  have hG := hq.differentiableAt.hasFDerivAt.inner ℝ hh
  have he : (fun p => inner ℝ (F p) (fderiv ℝ F p h)) =
      (fun p => inner ℝ h p) := funext (fun p => (hfirst p h).trans (real_inner_comm p h).symm)
  rw [he] at hG
  have hu := hG.unique (innerSL ℝ h).hasFDerivAt
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L k) hu
  change inner ℝ (F q) (fderiv ℝ F q 0+(fderiv ℝ (fderiv ℝ F) q k) h)+
    inner ℝ (fderiv ℝ F q k) (fderiv ℝ F q h) = inner ℝ h k at hv
  rw [map_zero,zero_add] at hv
  have hb := fderiv_fderiv_clm_comp F q hq (innerSL ℝ (F q))
  change fderiv ℝ (fderiv ℝ (fun p => inner ℝ (F q) (F p))) q = _ at hb
  rw [hb]
  change inner ℝ (F q) ((fderiv ℝ (fderiv ℝ F) q k) h) = _
  rw [(real_inner_comm h k).symm] at hv
  linarith

/-- An exact norm-preserving analytic map with compact scalar pairing
Hessian has a compact NORMAL derivative defect. This is sufficient for
a closed-range argument; no Fourier-remainder hypothesis is supplied. -/
theorem isCompactOperator_id_sub_adjoint_comp_fderiv_of_norm_map
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : E → Y) (hF : AnalyticOnNhd ℝ F univ) (hn : ∀ p, ‖F p‖ = ‖p‖) (q : E)
    (hc : IsCompactOperator (fderiv ℝ (fderiv ℝ (fun p => inner ℝ (F q) (F p))) q)) :
    IsCompactOperator (ContinuousLinearMap.id ℝ E-
      (fderiv ℝ F q).adjoint.comp (fderiv ℝ F q)) := by
  let H := fderiv ℝ (fderiv ℝ (fun p => inner ℝ (F q) (F p))) q
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let K := R.comp H
  have hK : IsCompactOperator K := hc.clm_comp R
  have he : K = ContinuousLinearMap.id ℝ E-(fderiv ℝ F q).adjoint.comp (fderiv ℝ F q) := by
    ext k
    apply ext_inner_right ℝ
    intro h
    have hKH : inner ℝ (K k) h = H k h := by
      have hh := congrArg (fun L : E →L[ℝ] ℝ => L h)
        ((InnerProductSpace.toDual ℝ E).apply_symm_apply (H k))
      exact hh
    rw [hKH]
    change H k h = inner ℝ (k-(fderiv ℝ F q).adjoint (fderiv ℝ F q k)) h
    rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
    exact secondDerivative_pairing_of_norm_map F hF hn q k h
  rw [←he]
  exact hK

end NLS.FunctionalAnalysis
