import NLS.ComplexAnalysis.EntireLimit
import NLS.ComplexAnalysis.LocalAnalyticSquareRoot
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
import Mathlib.Topology.MetricSpace.Algebra

/-! # Entire convergence descended through a quadratic spectral coordinate

Local square-root charts give convergence away from zero. Entire-limit
removal fills the exceptional energy, including locally uniform convergence.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem tendstoLocallyUniformlyOn_of_square_pullback
    (P : ℕ → ℂ → ℂ) (G : ℂ → ℂ) (hP : ∀ n, Differentiable ℂ (P n)) (hG : Continuous G)
    (h : TendstoLocallyUniformlyOn (fun n z => (2*z)*P n (z^2))
      (fun z => (2*z)*G (z^2)) atTop univ) :
    TendstoLocallyUniformlyOn P G atTop univ := by
  have hlocal (x : ℂ) (hx : x ≠ 0) : ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
      TendstoLocallyUniformlyOn P G atTop U := by
    have hw : Complex.sqrt x ≠ 0 := by
      intro he
      have hs := sq_sqrt x
      rw [he,zero_pow (by decide : 2 ≠ 0)] at hs
      exact hx hs.symm
    obtain ⟨U,hU,hxU,r,hr,_,hroot⟩ := exists_local_analytic_squareRoot (fun z : ℂ => z)
      x (Complex.sqrt x) analyticAt_id hw (sq_sqrt x).symm
    have hc := hr.continuousOn
    have hf := h.comp r (fun _ _ => mem_univ _) hc
    have hi : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => (2*r z)⁻¹)
        (fun z => (2*r z)⁻¹) atTop U := by
      intro v hv z _
      exact ⟨univ,Filter.univ_mem,Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
    have hfc : ContinuousOn (fun z : ℂ => (2*r z)*G ((r z)^2)) U :=
      (continuousOn_const.mul hc).mul (hG.continuousOn.comp (hc.pow 2) (fun _ _ => mem_univ _))
    have hic : ContinuousOn (fun z : ℂ => (2*r z)⁻¹) U :=
      (continuousOn_const.mul hc).inv₀ (fun z hz => mul_ne_zero (by norm_num) (hroot z hz).1)
    have hm : TendstoLocallyUniformlyOn
        (fun n z => ((2*r z)*P n ((r z)^2))*(2*r z)⁻¹)
        (fun z => ((2*r z)*G ((r z)^2))*(2*r z)⁻¹) atTop U := by
      simpa only [Pi.mul_apply,Function.comp_def] using! hf.mul₀ hi hfc hic
    have hl (n : ℕ) (z : ℂ) (hz : z ∈ U) :
        ((2*r z)*P n ((r z)^2))*(2*r z)⁻¹ = P n z := by
      rw [(hroot z hz).2]
      field_simp [(hroot z hz).1]
    have hg (z : ℂ) (hz : z ∈ U) :
        ((2*r z)*G ((r z)^2))*(2*r z)⁻¹ = G z := by
      rw [(hroot z hz).2]
      field_simp [(hroot z hz).1]
    exact ⟨U,hU,hxU,(hm.congr hl).congr_right hg⟩
  have hoff : TendstoLocallyUniformlyOn P G atTop ({(0 : ℂ)}ᶜ) := by
    intro v hv x hx
    obtain ⟨U,hU,hxU,hconv⟩ := hlocal x hx
    obtain ⟨T,hT,hb⟩ := hconv v hv x hxU
    rw [hU.nhdsWithin_eq hxU] at hT
    exact ⟨T,nhdsWithin_le_nhds hT,hb⟩
  have hlim := tendstoLocallyUniformlyOn_entireSequenceLimit P hP {(0 : ℂ)}
    (countable_singleton _) G hoff
  have heq := entireSequenceLimit_eqOn P hP {(0 : ℂ)} (countable_singleton _) G hoff
  have hcont := (analyticOnNhd_entireSequenceLimit P hP {(0 : ℂ)}
    (countable_singleton _) G hoff).continuous
  have he : entireSequenceLimit P = G := Continuous.ext_on (dense_compl_singleton 0) hcont hG heq
  simpa only [he] using hlim

end NLS.ComplexAnalysis
