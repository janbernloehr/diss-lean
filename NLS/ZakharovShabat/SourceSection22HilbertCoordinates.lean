import NLS.ZakharovShabat.SourceSection22PhaseSeparation
import NLS.SequenceSpaces.HilbertEnergyDivergence

/-! # Arbitrary Hilbert approximations in Section 22

The complex-coordinate half-sum energy is exactly the physical mass.
Original frequencies agree across the Hilbert and larger source exponents.
Every Hilbert coordinate approximation of a non-Hilbert image point has
diverging ordinary frequency and the literal half-amplitude separation.
Real approximating coordinates eventually lie in the actual original image.
-/
noncomputable section

open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The literal half-sum energy of the original complex Hilbert coordinates
is the physical mass, with exactly the source normalization. -/
theorem hilbert_complex_map_energy_eq_mass
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    (‖(sourceComplexBirkhoffMap (by simp) (by norm_num) s φ.val).1‖^2+
      ‖(sourceComplexBirkhoffMap (by simp) (by norm_num) s φ.val).2‖^2)/2 =
      sourceOrdinaryMass (by rfl) φ := by
  let z := sourceComplexBirkhoffMap (by simp) (by norm_num) s φ.val
  have hr : z.2 = star z.1 := by
    ext n
    exact D.complex_map_real φ n
  have hn : ‖z.2‖ = ‖z.1‖ := by rw [hr,norm_star]
  have ha (n : ℤ) : (sourceComplexAction (by simp) (by norm_num) n φ.val).re = ‖z.1 n‖^2 := by
    rw [← D.complex_map_action φ.val (D.real_subset φ.property) n,D.complex_map_real φ n]
    simp only [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq,z]
  change (‖z.1‖^2+‖z.2‖^2)/2 = _
  rw [sourceOrdinaryMass_eq_tsum (by simp) (by norm_num)]
  calc
    _ = ‖z.1‖^2 := by rw [hn]; ring
    _ = ∑' n : ℤ, ‖z.1 n‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z.1
    _ = _ := tsum_congr (fun n => (ha n).symm)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData

namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
  {W₀₂ W₂ V₂ Wa₂ B₂ U₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₀₂ W₂ V₂ s₂}
  {A₂ : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa₂ s₂}
  (Q₂ : SourceSection20Data D₂ A₂ B₂ U₂)
include Q Q₂

/-- The literal coordinate mass shift at every Hilbert source equals its
original ordinary frequency, even when the image inverse uses exponent p.
The two original atlases are connected by coefficient compatibility. -/
theorem hilbert_coordinate_frequency_eq_ordinary (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    A.phaseFrequency (D.complex.realImageInverse (Birkhoff.decodeReal
      (((Coeff.exponentInclusion h2p).prodMap (Coeff.exponentInclusion h2p))
        (sourceComplexBirkhoffMap (by simp) (by norm_num) s₂ φ.val)))) n +
      4*((‖(sourceComplexBirkhoffMap (by simp) (by norm_num) s₂ φ.val).1‖^2+
        ‖(sourceComplexBirkhoffMap (by simp) (by norm_num) s₂ φ.val).2‖^2)/2) =
      A₂.ordinaryPhaseFrequency (by rfl) φ n := by
  let ψ : realTypeSourceSubmodule p := realTypeSourceExponentInclusion h2p ⟨φ.val,φ.property⟩
  have he : ((Coeff.exponentInclusion h2p).prodMap (Coeff.exponentInclusion h2p))
      (sourceComplexBirkhoffMap (by simp) (by norm_num) s₂ φ.val) =
      sourceComplexBirkhoffMap hp hp1 s ψ.val := D₂.complex.complex_map_exponent D.complex h2p φ
  rw [he,
    ← D.complex.encode_real_map ψ,Birkhoff.decodeReal_encodeReal,D.complex.realImageInverse_real_map,
    D₂.complex.hilbert_complex_map_energy_eq_mass]
  have hf := A.renormalizedFrequency_real_eq_of_coefficients A₂
    Q.roots.toSourcePsiIsolatingComplexExtension Q₂.roots.toSourcePsiIsolatingComplexExtension
    ψ φ (fun _ => ⟨rfl,rfl⟩) n
  simp only [SourceAbelianMomentAtlas.phaseFrequency,SourceAbelianMomentAtlas.ordinaryPhaseFrequency,hf]

end NLS.ZakharovShabat.SourceSection20Data


open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The literal mass-shifted coordinate frequency diverges along every
Hilbert-pair approximation to a non-Hilbert coordinate image point.
The original renormalized frequency and actual local image inverse are used.
On conjugate pairs the half-sum energy is the real coordinate mass. -/
theorem tendsto_hilbert_coordinate_frequency_atTop (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun n : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n‖^2))
    (z : ι → Coeff 2 × Coeff 2)
    (hz : Tendsto (fun j => ((Coeff.exponentInclusion h2p).prodMap
      (Coeff.exponentInclusion h2p)) (z j)) l
      (𝓝 (sourceComplexBirkhoffMap hp hp1 s φ.val))) (n : ℤ) :
    Tendsto (fun j => A.phaseFrequency (D.complex.realImageInverse
      (Birkhoff.decodeReal (((Coeff.exponentInclusion h2p).prodMap
        (Coeff.exponentInclusion h2p)) (z j)))) n +
      4*((‖(z j).1‖^2+‖(z j).2‖^2)/2)) l atTop := by
  have hbase : Birkhoff.decodeReal (sourceComplexBirkhoffMap hp hp1 s φ.val) =
      sourceRealBirkhoffMap hp hp1 s φ := by
    rw [← D.complex.encode_real_map, Birkhoff.decodeReal_encodeReal]
  have hd : Tendsto (fun j => Birkhoff.decodeReal (((Coeff.exponentInclusion h2p).prodMap
      (Coeff.exponentInclusion h2p)) (z j))) l (𝓝 (sourceRealBirkhoffMap hp hp1 s φ)) := by
    simpa only [hbase,Function.comp_def] using (Birkhoff.decodeReal.continuous.tendsto _).comp hz
  have hi : Tendsto (fun j => D.complex.realImageInverse
      (Birkhoff.decodeReal (((Coeff.exponentInclusion h2p).prodMap
        (Coeff.exponentInclusion h2p)) (z j)))) l (𝓝 φ) := by
    simpa only [D.complex.realImageInverse_real_map,Function.comp_def] using
      (D.complex.realImageInverse_analytic _ (mem_range_self φ)).continuousAt.tendsto.comp hd
  have hf := (A.continuous_phaseFrequency Q.roots D.roots_open D.roots_real_subset n).continuousAt.tendsto.comp hi
  have heval (k : ℤ) : Tendsto (fun j => (z j).1 k) l
      (𝓝 ((sourceComplexBirkhoffMap hp hp1 s φ.val).1 k)) := by
    have hfirst := hz.fst_nhds
    have hk := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).continuous.tendsto _).comp hfirst
    exact hk
  have he := Coeff.tendsto_pair_energy_atTop_of_nonsummable_limit
    (fun k => (sourceComplexBirkhoffMap hp hp1 s φ.val).1 k) hφ z heval
  simpa only [Function.comp_def] using hf.add_atTop (he.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

/-- Every convergent real coordinate approximation is eventually in the
actual original image. The original inverse then recovers those complex
coordinates and remains in the unchanged source frequency neighborhood. -/
theorem eventually_conjugate_coordinate_image {ι : Type*} {l : Filter ι}
    (φ : realTypeSourceSubmodule p) (z : ι → Coeff p × Coeff p)
    (hz : Tendsto z l (𝓝 (sourceComplexBirkhoffMap hp hp1 s φ.val)))
    (hr : ∀ j, Birkhoff.IsConjugatePair (z j)) :
    ∀ᶠ j in l,
      Birkhoff.decodeReal (z j) ∈ range (sourceRealBirkhoffMap hp hp1 s) ∧
      sourceComplexBirkhoffMap hp hp1 s (D.complex.realImageInverse (Birkhoff.decodeReal (z j))).val = z j ∧
      (D.complex.realImageInverse (Birkhoff.decodeReal (z j))).val ∈ U := by
  have hbase : Birkhoff.decodeReal (sourceComplexBirkhoffMap hp hp1 s φ.val) =
      sourceRealBirkhoffMap hp hp1 s φ := by
    rw [← D.complex.encode_real_map,Birkhoff.decodeReal_encodeReal]
  have hd : Tendsto (fun j => Birkhoff.decodeReal (z j)) l
      (𝓝 (sourceRealBirkhoffMap hp hp1 s φ)) := by
    simpa only [hbase,Function.comp_def] using (Birkhoff.decodeReal.continuous.tendsto _).comp hz
  filter_upwards [hd.eventually (D.complex.real_image_open.mem_nhds (mem_range_self φ))] with j hj
  refine ⟨hj,?_,Q.real_subset (D.complex.realImageInverse (Birkhoff.decodeReal (z j))).property⟩
  rw [← D.complex.encode_real_map,D.complex.real_map_realImageInverse _ hj,
    Birkhoff.encodeReal_decodeReal _ (hr j)]

/-- The literal separation construction for arbitrary real Hilbert
coordinate approximations. The original inverse is eventually genuine;
no finite-gap or smooth restriction is imposed on the approximations. -/
theorem exists_hilbert_coordinate_separation (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun k : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 k‖^2))
    (z : ℕ → Coeff 2 × Coeff 2) (hr : ∀ j, Birkhoff.IsConjugatePair (z j))
    (hz : Tendsto (fun j => ((Coeff.exponentInclusion h2p).prodMap
      (Coeff.exponentInclusion h2p)) (z j)) atTop
      (𝓝 (sourceComplexBirkhoffMap hp hp1 s φ.val)))
    (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n ≠ 0) (T : ℝ) (hT : 0 < T) :
    let emb := (Coeff.exponentInclusion h2p).prodMap (Coeff.exponentInclusion h2p)
    let freq := fun j => A.phaseFrequency (D.complex.realImageInverse (Birkhoff.decodeReal (emb (z j)))) n +
      4*((‖(z j).1‖^2+‖(z j).2‖^2)/2)
    let amp := fun j => Coeff.exponentInclusion h2p (z j).1
    (∀ᶠ j in atTop, sourceComplexBirkhoffMap hp hp1 s
      (D.complex.realImageInverse (Birkhoff.decodeReal (emb (z j)))).val = emb (z j)) ∧
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ time : ℕ → ℝ,
      (∀ m, time m ∈ Icc (-T) T) ∧
      (∀ m, 1 ≤ ‖Complex.exp ((((-time m*(freq (r (m+1))-freq (r m)) : ℝ) : ℂ))*Complex.I)-1‖ ∧
        ‖amp (r m) n‖-‖amp (r (m+1))-amp (r m)‖ ≤
          ‖Complex.exp ((((-time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*amp (r (m+1)) n-
            Complex.exp ((((-time m*freq (r m) : ℝ) : ℂ))*Complex.I)*amp (r m) n‖) ∧
      ∀ᶠ m : ℕ in atTop, ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n‖/2 ≤
        ‖Complex.exp ((((-time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*amp (r (m+1)) n-
          Complex.exp ((((-time m*freq (r m) : ℝ) : ℂ))*Complex.I)*amp (r m) n‖ := by
  dsimp only
  have hfreq := Q.tendsto_hilbert_coordinate_frequency_atTop h2p φ hφ z hz n
  have himage := Q.eventually_conjugate_coordinate_image φ
    (fun j => ((Coeff.exponentInclusion h2p).prodMap (Coeff.exponentInclusion h2p)) (z j)) hz
    (fun j k => hr j k)
  have hamp : Tendsto (fun j => Coeff.exponentInclusion h2p (z j).1) atTop
      (𝓝 (sourceComplexBirkhoffMap hp hp1 s φ.val).1) := hz.fst_nhds
  obtain ⟨r,hmono,time,ht,hb,he⟩ := Coeff.exists_phase_separated_subsequence _ hfreq _ _ hamp n hn T hT
  refine ⟨himage.mono (fun j hj => hj.2.1),r,hmono,fun m => -time m,fun m => ⟨?_,?_⟩,?_,?_⟩
  · linarith [(ht m).2]
  · linarith [(ht m).1]
  · simpa only [neg_neg] using hb
  · simpa only [neg_neg] using he

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
  {W₀₂ W₂ V₂ Wa₂ B₂ U₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₀₂ W₂ V₂ s₂}
  {A₂ : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa₂ s₂}
  (Q₂ : SourceSection20Data D₂ A₂ B₂ U₂)
include Q Q₂

/-- The actual original Hilbert ordinary frequencies diverge along every
Hilbert approximation whose coordinates converge to a non-Hilbert image
point. The approximation is not required to be finite-gap or smooth. -/
theorem tendsto_original_hilbert_ordinary_frequency_atTop (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun k : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 k‖^2))
    (ψ : ι → realTypeSourceSubmodule 2)
    (hψ : Tendsto (fun j => ((Coeff.exponentInclusion h2p).prodMap (Coeff.exponentInclusion h2p))
      (sourceComplexBirkhoffMap (by simp) (by norm_num) s₂ (ψ j).val)) l
      (𝓝 (sourceComplexBirkhoffMap hp hp1 s φ.val))) (n : ℤ) :
    Tendsto (fun j => A₂.ordinaryPhaseFrequency (by rfl) (ψ j) n) l atTop := by
  have ht := Q.tendsto_hilbert_coordinate_frequency_atTop h2p φ hφ
    (fun j => sourceComplexBirkhoffMap (by simp) (by norm_num) s₂ (ψ j).val) hψ n
  simpa only [Q.hilbert_coordinate_frequency_eq_ordinary Q₂ h2p] using ht

end NLS.ZakharovShabat.SourceSection20Data
