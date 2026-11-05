import NLS.KdV.HillEndpointDirichletPrimitives
import NLS.KdV.HillFiniteNormingGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Genuine finite families of physical endpoint Abelian primitives have H1
cotangents in the finite norming span. These cotangents represent their actual
source derivatives and have zero genuine Gardner brackets pairwise. -/
theorem exists_hillFiniteEndpointPrimitives_H1_cotangents
    (q : RealPeriodOneHillPotential) (s : Finset ℕ)
    (hgap : ∀ j∈s, hillRealGapHalfLength q.val q.property.1 q.property.2 (j+1)≠0)
    (hlog : ∀ j∈s, hillDirichletLogMultiplier q.val q.property.1 q.property.2 (j+1) (by omega)=0) :
    ∃ B ε : ℕ → ℕ → Coeff 2 → ℂ, ∃ c : ℕ → ℕ → ℂ,
      (∀ n : ℕ, ∀ j∈s,
        AnalyticAt ℂ (B n j) (SpectralWeight.one.toCoeff q.val) ∧
        AnalyticAt ℂ (ε n j) (SpectralWeight.one.toCoeff q.val) ∧
        (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 (j+1))
            (hillRealGapHalfLength p.val p.property.1 p.property.2 (j+1)) (ε n j (SpectralWeight.one.toCoeff p.val))=
              (hillDirichletEnergy p.val p.property.1 p.property.2 (j+1) (by omega) : ℂ) ∧
          Complex.sin (ε n j (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 (j+1) (by omega) ∧
          B n j (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2
            (n+1) (by omega) (j+1) (ε n j (SpectralWeight.one.toCoeff p.val)))) ∧
      (∀ n : ℕ, AnalyticAt ℂ (fun p => ∑ j∈s,B n j p) (SpectralWeight.one.toCoeff q.val) ∧
        ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
          SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
          (fderiv ℂ (fun p => ∑ j∈s,B n j p) (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
            hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillFiniteNormingGradient q s (c n))) ∧
      (∀ n : ℕ,
        AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n))) 0 1 ∧
        MemLp (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
        MemLp (deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n)))) 2 (volume.restrict (Ioc (0 : ℝ) 1))) ∧
      ∀ n m : ℕ,
        (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c n)) x*
          deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s (c m))) x)=0 := by
  classical
  have hex (n j : ℕ) (hj : j∈s) := exists_hillDirichletPrimitive_endpoint_norming_cotangent h0q h0r
    q (n+1) (j+1) (by omega) (by omega) (hgap j hj) (hlog j hj)
  choose B ε e c he hB hε hε0 hphysical hder using hex
  let BB (n j : ℕ) : Coeff 2 → ℂ := if hj : j∈s then B n j hj else 0
  let EE (n j : ℕ) : Coeff 2 → ℂ := if hj : j∈s then ε n j hj else 0
  let CC (n j : ℕ) : ℂ := if hj : j∈s then c n j hj else 0
  have hBB (n j : ℕ) (hj : j∈s) : AnalyticAt ℂ (BB n j) (SpectralWeight.one.toCoeff q.val) := by
    simpa only [BB,dif_pos hj] using hB n j hj
  refine ⟨BB,EE,CC,?_,?_,fun n => hillFiniteNormingGradient_H1 q s (CC n),
    fun n m => hillFiniteNormingGradient_GardnerBracket_eq_zero q s s (CC n) (CC m)⟩
  · intro n j hj
    refine ⟨hBB n j hj,?_,?_⟩
    · simpa only [EE,dif_pos hj] using hε n j hj
    · filter_upwards [hphysical n j hj] with p hp
      simpa only [BB,EE,dif_pos hj] using ⟨hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  · intro n
    refine ⟨Finset.analyticAt_fun_sum _ (fun j hj => hBB n j hj),?_⟩
    intro h heven
    rw [fderiv_fun_sum (fun j hj => (hBB n j hj).differentiableAt)]
    simp only [sum_apply,hillFiniteNormingGradient,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [BB,CC,dif_pos hj] using hder n j hj h heven

end NLS.KdV
