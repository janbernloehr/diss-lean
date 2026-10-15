import NLS.Fourier.DiscreteParseval
import NLS.Fourier.PeriodicL1Fourier
import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equally spaced sampling of the physical circle

Normalized sample averages converge to Haar integration for every continuous
function. Uniform operator bounds and the dense span of Fourier modes extend
character orthogonality to arbitrary continuous functions and norm powers.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- Equally spaced points on the actual circle of period L. -/
def circleGridPoint (N : ℕ) [NeZero N] (j : ZMod N) : AddCircle L :=
  ((j.val : ℝ)*L/N : ℝ)

theorem fourier_circleGridPoint (N : ℕ) [NeZero N] (j : ZMod N) (n : ℤ) :
    fourier n (circleGridPoint (L := L) N j) = ZMod.stdAddChar ((n : ZMod N)*j) := by
  have hc : ((n*(j.val : ℤ) : ℤ) : ZMod N) = (n : ZMod N)*j := by simp
  rw [← hc,ZMod.stdAddChar_coe]
  change fourier n (((j.val : ℝ)*L/N : ℝ) : AddCircle L) = _
  rw [fourier_coe_apply]
  push_cast
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne']

/-- The normalized average of a continuous function over an N-point grid. -/
def circleGridAverage (N : ℕ) [NeZero N] : C(AddCircle L,ℂ) →L[ℂ] ℂ :=
  let F : C(AddCircle L,ℂ) →ₗ[ℂ] ℂ := {
    toFun f := (N:ℂ)⁻¹ * ∑ j : ZMod N, f (circleGridPoint N j)
    map_add' f g := by simp [Finset.sum_add_distrib,mul_add]
    map_smul' c f := by simp [Finset.mul_sum,mul_left_comm] }
  F.mkContinuous 1 (by
    intro f
    change ‖(N:ℂ)⁻¹ * ∑ j : ZMod N, f (circleGridPoint N j)‖ ≤ 1*‖f‖
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ (N:ℝ)⁻¹*∑ j : ZMod N, ‖f (circleGridPoint N j)‖ := by gcongr; exact norm_sum_le _ _
      _ ≤ (N:ℝ)⁻¹*∑ _j : ZMod N, ‖f‖ := by gcongr; exact f.norm_coe_le_norm _
      _ = _ := by simp [NeZero.ne N])

theorem circleGridAverage_fourier (N : ℕ) [NeZero N] (n : ℤ) :
    circleGridAverage (L := L) N (fourier n) = if (n : ZMod N) = 0 then 1 else 0 := by
  change (N:ℂ)⁻¹ * ∑ j : ZMod N, fourier n (circleGridPoint N j) = _
  simp_rw [fourier_circleGridPoint]
  rw [sum_stdAddChar_mul]
  split_ifs <;> simp [NeZero.ne N]

theorem norm_circleGridAverage_le (N : ℕ) [NeZero N] : ‖circleGridAverage (L := L) N‖ ≤ 1 := by
  unfold circleGridAverage
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Integration against the probability Haar measure on the physical circle. -/
def circleMean : C(AddCircle L,ℂ) →L[ℂ] ℂ :=
  circleL1Functional (fun _ => 1) (integrable_const 1)

theorem circleMean_apply (f : C(AddCircle L,ℂ)) :
    circleMean f = ∫ x, f x ∂AddCircle.haarAddCircle := by
  change (∫ x, (1:ℂ)*f x ∂AddCircle.haarAddCircle) = _
  simp only [one_mul]

theorem circleMean_fourier (n : ℤ) :
    circleMean (L := L) (fourier n) = if n = 0 then 1 else 0 := by
  rw [circleMean_apply]
  have h := congrFun (fourierCoeff_fourier (T := L) 0) (-n)
  simpa [fourierCoeff,Pi.single_apply] using h

theorem tendsto_circleGridAverage_fourier (n : ℤ) :
    Tendsto (fun N : ℕ => circleGridAverage (L := L) (N+1) (fourier n)) atTop
      (𝓝 (circleMean (L := L) (fourier n))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  rw [circleGridAverage_fourier,circleMean_fourier]
  by_cases hn : n = 0
  · simp [hn]
  · have hcast : (n : ZMod (N+1)) ≠ 0 := by
      intro he
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd n (N+1)).mp he
      have hd' : N+1 ∣ n.natAbs := by
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
      have hb := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd'
      omega
    simp [hn,hcast]

/-- Grid averages converge for every continuous function, by density of Fourier polynomials. -/
theorem tendsto_circleGridAverage (f : C(AddCircle L,ℂ)) :
    Tendsto (fun N : ℕ => circleGridAverage (L := L) (N+1) f) atTop (𝓝 (circleMean f)) := by
  let S : Submodule ℂ C(AddCircle L,ℂ) := {
    carrier := {f | Tendsto (fun N : ℕ => circleGridAverage (L := L) (N+1) f) atTop (𝓝 (circleMean f))}
    zero_mem' := by simp only [mem_ofPred_eq,map_zero]; exact tendsto_const_nhds
    add_mem' := by
      intro f g hf hg
      simpa only [mem_ofPred_eq,map_add] using hf.add hg
    smul_mem' := by
      intro c f hf
      simpa only [mem_ofPred_eq,map_smul] using hf.const_smul c }
  have hb : ∃ C : ℝ, ∀ N : ℕ, ‖circleGridAverage (L := L) (N+1)‖ ≤ C :=
    ⟨1,fun N => norm_circleGridAverage_le (N+1)⟩
  have heq : Equicontinuous (fun N : ℕ => (circleGridAverage (L := L) (N+1) : C(AddCircle L,ℂ) → ℂ)) :=
    ((NormedSpace.equicontinuous_TFAE (fun N : ℕ => circleGridAverage (L := L) (N+1))).out 5 1).mp
      hb
  have hc : IsClosed (S : Set C(AddCircle L,ℂ)) := heq.isClosed_setOfPred_tendsto circleMean.continuous
  have hs : Submodule.span ℂ (range (@fourier L)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact tendsto_circleGridAverage_fourier n
  have hh := Submodule.topologicalClosure_minimal _ hs hc
  rw [span_fourier_closure_eq_top] at hh
  exact hh (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(AddCircle L,ℂ)))

theorem tendsto_circleGridAverage_norm_rpow (f : C(AddCircle L,ℂ)) {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)⁻¹ * ∑ j : ZMod (N+1), ‖f (circleGridPoint (N+1) j)‖^q)
      atTop (𝓝 (∫ x, ‖f x‖^q ∂AddCircle.haarAddCircle)) := by
  let g : C(AddCircle L,ℂ) := ⟨fun x => ((‖f x‖^q : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.norm.rpow_const (fun _ => Or.inr hq))⟩
  have h := Complex.continuous_re.tendsto (circleMean g) |>.comp (tendsto_circleGridAverage g)
  have he (N : ℕ) : (circleGridAverage (N+1) g).re =
      ((N+1:ℕ):ℝ)⁻¹ * ∑ j : ZMod (N+1), ‖f (circleGridPoint (N+1) j)‖^q := by
    change (((N+1:ℕ):ℂ)⁻¹ * ∑ j : ZMod (N+1), ((‖f (circleGridPoint (N+1) j)‖^q : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_sum,show ((N+1:ℕ):ℂ) = (((N+1:ℕ):ℝ):ℂ) by simp,
      ← Complex.ofReal_inv,← Complex.ofReal_mul,Complex.ofReal_re]
  have hlim : (circleMean g).re = ∫ x, ‖f x‖^q ∂AddCircle.haarAddCircle := by
    rw [circleMean_apply]
    change (∫ x, ((‖f x‖^q : ℝ) : ℂ) ∂AddCircle.haarAddCircle).re = _
    rw [integral_complex_ofReal,Complex.ofReal_re]
  simpa only [Function.comp_def,he,hlim] using h

end NLS.Fourier
