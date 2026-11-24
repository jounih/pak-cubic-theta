module

public import ActionSeparation
public import PakStokes.PhysicalPhases
public import PakStokes.PhysicalBackground
public import PakStokes.RegularCube
public import PakStokes.PhysicalSpectrum
public import Laplace
public import CubeLinear
public import CubicJump
public import CubicLateral
public import CutContour
public import KernelAnalytic
public import LaplaceDerivative
public import BorelTransfer
public import CubicActions
public import MixedActions
public import PakStokes.PakTransfer
public import PakStokes.PhysicalJacobian
public import PakStokes.PhysicalParity
public import PakStokes.ThetaControls
import all PakStokes.PhysicalJacobian
import all PakStokes.RayAlgebra
import all PakStokes.PhysicalParity
import all PakStokes.RegularCube
public import Mathlib.Algebra.MvPolynomial.Eval

/-! Coefficient separation on a common ray, allowing the two half-power parities.
A unit phase permits a tilted ray where the lateral Borel kernels are analytic. -/
public section
namespace CubicTheta
open Real Filter
open scoped Topology

def Leading (a : ℝ → ℂ) (v : ℝ) (z : ℂ) :=
  Tendsto (fun x : ℝ ↦ x^v • a x) atTop (𝓝 z)

private theorem leading_shift {a : ℝ → ℂ} {v : ℝ} {z : ℂ}
    (h : Leading a v z) (d : ℝ) :
    Leading (fun x ↦ x^d • a x) (v-d) z := by
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [smul_smul, ← rpow_add hx, sub_add_cancel]

private theorem leading_add_of_lt {a b : ℝ → ℂ} {v t : ℝ} {z y : ℂ}
    (ha : Leading a v z) (hb : Leading b t y) (hlt : v < t) :
    Leading (fun x ↦ a x + b x) v z := by
  have hp : Tendsto (fun x : ℝ ↦ x^(v-t)) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr hlt))
  have hz : Tendsto (fun x : ℝ ↦ x^v • b x) atTop (𝓝 0) := by
    have h := hp.smul hb
    rw [zero_smul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [smul_smul, ← rpow_add hx, sub_add_cancel]
  simpa [Leading, smul_add] using ha.add hz

/-- Two ordinary Laplace sums shifted by powers in different classes modulo
the integers cannot cancel their leading terms. -/
theorem parity_leading (a b : ℝ → ℂ) (s t : ℝ)
    (disjoint : ∀ n m : ℕ, (n:ℝ)-s ≠ (m:ℝ)-t)
    (ha : (∀ᶠ x : ℝ in atTop, a x = 0) ∨
      ∃ (n : ℕ) (z : ℂ), z ≠ 0 ∧ Leading a n z)
    (hb : (∀ᶠ x : ℝ in atTop, b x = 0) ∨
      ∃ (m : ℕ) (y : ℂ), y ≠ 0 ∧ Leading b m y) :
    (∀ᶠ x : ℝ in atTop, x^s • a x + x^t • b x = 0) ∨
    (∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧ Leading (fun x ↦ x^s • a x + x^t • b x) v z) := by
  rcases ha with ha | ⟨n,z,hz,ha⟩ <;> rcases hb with hb | ⟨m,y,hy,hb⟩
  · left; filter_upwards [ha,hb] with x h1 h2; simp [h1,h2]
  · right
    refine ⟨(m:ℝ)-t,y,hy,(leading_shift hb t).congr' ?_⟩
    filter_upwards [ha] with x h; simp [h]
  · right
    refine ⟨(n:ℝ)-s,z,hz,(leading_shift ha s).congr' ?_⟩
    filter_upwards [hb] with x h; simp [h]
  · right
    rcases lt_or_gt_of_ne (disjoint n m) with h | h
    · exact ⟨_,_,hz,leading_add_of_lt (leading_shift ha s) (leading_shift hb t) h⟩
    · refine ⟨(m:ℝ)-t,y,hy,?_⟩
      simpa only [add_comm] using leading_add_of_lt (leading_shift hb t) (leading_shift ha s) h

theorem parity_dichotomy (a b : ℝ → ℂ) (s t : ℝ)
    (disjoint : ∀ n m : ℕ, (n:ℝ)-s ≠ (m:ℝ)-t)
    (ha : (∀ᶠ x : ℝ in atTop, a x = 0) ∨
      ∃ (n : ℕ) (z : ℂ), z ≠ 0 ∧ Leading a n z)
    (hb : (∀ᶠ x : ℝ in atTop, b x = 0) ∨
      ∃ (m : ℕ) (y : ℂ), y ≠ 0 ∧ Leading b m y) :
    (∀ᶠ x : ℝ in atTop, x^s • a x + x^t • b x = 0) ∨
    Detectable (fun x ↦ x^s • a x + x^t • b x) := by
  apply (parity_leading _ _ _ _ disjoint ha hb).imp_right
  rintro ⟨_,_,hz,hl⟩
  exact detectable_of_leading hz hl

def RayKernel (F : ℝ → ℂ) : Prop :=
  AnalyticOnNhd ℝ F (Set.Ici 0) ∧ ∃ C D : ℝ, 0 ≤ D ∧ ∀ u > 0, ‖F u‖ ≤ C * exp (D*u)

/-- Every kernel needed by a physical background derivative satisfies the
analyticity and growth hypothesis used in coefficient separation. -/
theorem physical_background_moment_kernel (j : ℕ) : RayKernel (Physical.BackgroundInverse.momentKernel j) := by
  obtain ⟨C,hC⟩ := Physical.BackgroundInverse.momentKernel_growth j
  exact ⟨Physical.BackgroundInverse.momentKernel_analytic j,C,1,zero_le_one,by simpa using hC⟩

private theorem kernel_orders {F : ℝ → ℂ} (h : RayKernel F) :
    (∀ᶠ x : ℝ in atTop, raySum F x = 0) ∨
    ∃ (n : ℕ) (z : ℂ), z ≠ 0 ∧ Leading (raySum F) n z := by
  obtain ⟨ha,C,D,hD,hg⟩ := h
  rcases raySum_dichotomy ha hD hg with hz | ⟨n,z,hz,hl⟩
  · exact .inl ((eventually_gt_atTop (0:ℝ)).mono hz)
  · exact .inr ⟨n,z,hz, by simpa [Leading] using hl⟩

/-- End-to-end uniqueness from analytic kernels, an absolutely summable envelope
and zero total. The oscillating factors on a tilted ray need only have unit norm. -/
theorem separate_ray_sums (w : ℕ → ℝ) (hw : StrictMono w) (a : ℕ → ℝ → ℂ)
    (F G : ℕ → ℝ → ℂ) (s t : ℕ → ℝ) (unit : ℕ → ℝ → ℂ)
    (hunit : ∀ i x, ‖unit i x‖ = 1)
    (hF : ∀ i, RayKernel (F i)) (hG : ∀ i, RayKernel (G i))
    (disjoint : ∀ i (n m : ℕ), (n:ℝ)-s i ≠ (m:ℝ)-t i)
    (repr : ∀ i, ∀ᶠ x : ℝ in atTop, a i x = x^(s i) • raySum (F i) x + x^(t i) • raySum (G i) x)
    (b : ℕ → ℝ) (hb : Summable b) (K reserve : ℝ)
    (major : ∀ᶠ x : ℝ in atTop, ∀ i, ‖a i x‖ ≤ b i * exp (w i*reserve) * x^K)
    (zeroSum : ∀ᶠ x : ℝ in atTop,
      HasSum (fun i ↦ exp (-w i*x) • (unit i x * a i x)) 0) :
    ∀ i, ∀ᶠ x : ℝ in atTop, a i x = 0 := by
  have hnorm (i x) : ‖unit i x * a i x‖ = ‖a i x‖ := by rw [norm_mul,hunit,one_mul]
  have hd i := parity_dichotomy _ _ _ _ (disjoint i) (kernel_orders (hF i)) (kernel_orders (hG i))
  have h := separate_actions w hw (fun i x ↦ unit i x * a i x) b hb K reserve
    (by simpa only [hnorm] using major) zeroSum (fun i ↦ by
      rcases hd i with hz | ⟨v,c,hc,hl⟩
      · left; filter_upwards [hz,repr i] with x hx hr; rw [hr,hx,mul_zero]
      · right; refine ⟨v,c,hc,?_⟩
        filter_upwards [hl,repr i] with x hx hr; rwa [hnorm,hr])
  intro i
  filter_upwards [h i] with x hx
  apply norm_eq_zero.mp
  rw [← hnorm, hx, norm_zero]

/-- Regroup a zero polynomial expansion directly from its ungrouped terms.
The budget, the grouped majorant, and the grouped zero identity are derived. -/
theorem separate_wave_products {ι : Type*} (a : WaveExpansion ι)
    (g : ι → ℕ) (r : ℕ → ℂ) (hr : ∀ i, a.rate i = r (g i))
    (order : StrictMono (fun i ↦ (r i).re))
    (zero : ∀ᶠ x in atTop, a.value x = 0)
    (F G : ℕ → ℝ → ℂ) (s t : ℕ → ℝ)
    (hF : ∀ i, RayKernel (F i)) (hG : ∀ i, RayKernel (G i))
    (disjoint : ∀ i (n m : ℕ), (n:ℝ)-s i ≠ (m:ℝ)-t i)
    (repr : ∀ i, ∀ᶠ x : ℝ in atTop, a.groupAmplitude g i x =
      x^(s i) • raySum (F i) x + x^(t i) • raySum (G i) x) :
    ∀ i, ∀ᶠ x : ℝ in atTop, a.groupAmplitude g i x = 0 := by
  let phase (i : ℕ) (x : ℝ) := Complex.exp (↑(-(r i).im*x)*Complex.I)
  have unit (i x) : ‖phase i x‖ = 1 := by simp [phase,Complex.norm_exp]
  apply separate_ray_sums _ order _ F G s t phase unit hF hG disjoint repr
    (a.groupBudget g) (a.grouped_budget g) a.loss 1
  · simpa using a.grouped_bound g r hr
  filter_upwards [a.grouped_hasSum g r hr,zero] with x h hz
  rw [hz] at h
  apply h.congr_fun
  intro i
  symm
  change Complex.exp (-r i*x)*_ = (↑(Real.exp (-(r i).re*x)):ℂ) * (phase i x * _)
  unfold phase
  rw [Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

/-- Kernel version of physical-axis separation. Frequencies may have equal real
decay. Only their imaginary parts within each cluster must be distinct. -/
theorem separate_physical_ray_sums {ι : Type*} {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (a : WaveExpansion ι) (g : ι → Σ n, κ n) (w : ℕ → ℝ) (b : ∀ n, κ n → ℝ)
    (hr : ∀ i, a.rate i = ⟨w (g i).1,-b (g i).1 (g i).2⟩)
    (order : StrictMono w) (apart : ∀ n, Function.Injective (b n))
    (zero : ∀ᶠ x : ℝ in atTop, a.value x = 0)
    (F G : (Σ n, κ n) → ℝ → ℂ) (s t : (Σ n, κ n) → ℝ)
    (hF : ∀ k, RayKernel (F k)) (hG : ∀ k, RayKernel (G k))
    (disjoint : ∀ k (n m : ℕ), (n:ℝ)-s k ≠ (m:ℝ)-t k)
    (repr : ∀ k, ∀ᶠ x : ℝ in atTop, a.groupAmplitude g k x =
      x^(s k) • raySum (F k) x + x^(t k) • raySum (G k) x) :
    ∀ n (j : κ n), ∀ᶠ x : ℝ in atTop, a.groupAmplitude g ⟨n,j⟩ x = 0 := by
  apply separate_physical_products a g w b hr order apart zero
  intro k
  rcases parity_leading _ _ _ _ (disjoint k) (kernel_orders (hF k)) (kernel_orders (hG k))
    with hz | ⟨v,z,hn,hl⟩
  · left; filter_upwards [repr k,hz] with x hx hh; exact hx.trans hh
  · right; refine ⟨v,z,hn,hl.congr' ?_⟩
    filter_upwards [repr k] with x hx; rw [hx]

/-- Start with an identity in derivatives of the actual cube residual.
The real-rate ordering, finite clusters, absolute regrouping and zero total
are derived from the expression. Its two analytic kernel representations
per full complex action remain hypotheses. -/
theorem separate_cube_residual_identity (e : Physical.JetExpression)
    (zero : ∀ᶠ x : ℝ in atTop, e.eval x = 0)
    (F G : (Σ n, e.Frequency n) → ℝ → ℂ) (s t : (Σ n, e.Frequency n) → ℝ)
    (hF : ∀ k, RayKernel (F k)) (hG : ∀ k, RayKernel (G k))
    (disjoint : ∀ k (n m : ℕ), (n:ℝ)-s k ≠ (m:ℝ)-t k)
    (repr : ∀ k, ∀ᶠ x : ℝ in atTop, e.expansion.groupAmplitude e.group k x =
      x^(s k) • raySum (F k) x + x^(t k) • raySum (G k) x) :
    ∀ n (j : e.Frequency n), ∀ᶠ x : ℝ in atTop, e.expansion.groupAmplitude e.group ⟨n,j⟩ x = 0 := by
  apply separate_physical_ray_sums e.expansion e.group e.decay (fun _ j ↦ j.val)
    e.group_rate e.decay_strictMono (fun _ ↦ Subtype.val_injective) _ F G s t hF hG disjoint repr
  filter_upwards [e.expansion_value,zero] with x he hz
  exact he.trans hz

/-- Positive-temperature cube series with only the explicit endpoint and
gamma pole removed. All background derivatives are inserted as bounded
zero-action coefficients before the physical products are expanded. -/
theorem separate_regular_cube_identity (e : Physical.JetExpression)
    (zero : ∀ᶠ x : ℝ in atTop, e.evalRegular x = 0)
    (F G : (Σ n, e.withBackground.Frequency n) → ℝ → ℂ) (s t : (Σ n, e.withBackground.Frequency n) → ℝ)
    (hF : ∀ k, RayKernel (F k)) (hG : ∀ k, RayKernel (G k))
    (disjoint : ∀ k (n m : ℕ), (n:ℝ)-s k ≠ (m:ℝ)-t k)
    (repr : ∀ k, ∀ᶠ x : ℝ in atTop, e.withBackground.expansion.groupAmplitude e.withBackground.group k x =
      x^(s k) • raySum (F k) x + x^(t k) • raySum (G k) x) :
    ∀ n (j : e.withBackground.Frequency n), ∀ᶠ x : ℝ in atTop, e.withBackground.expansion.groupAmplitude e.withBackground.group ⟨n,j⟩ x = 0 := by
  apply separate_cube_residual_identity e.withBackground _ F G s t hF hG disjoint repr
  filter_upwards [e.withBackground_eval,zero] with x he hz
  exact he.trans hz

/-- All grouped representations follow from the coefficient leaves.
For a constant-coefficient differential polynomial these leaves are automatic. -/
theorem separate_admissible_regular_cube (e : Physical.JetExpression) (h : e.Admissible)
    (zero : ∀ᶠ x : ℝ in atTop, e.evalRegular x = 0) :
    ∀ n (j : e.withBackground.Frequency n), ∀ᶠ x : ℝ in atTop,
      e.withBackground.expansion.groupAmplitude e.withBackground.group ⟨n,j⟩ x = 0 := by
  choose F G s t hf hg apart repr using fun k ↦
    (Physical.JetExpression.group_parities (Physical.JetExpression.admissible_background h) k).kernels
  have weaken {K} (hk : RayDensity K) : RayKernel K := by
    obtain ⟨C,D,_,hD,he⟩ := hk.2
    exact ⟨hk.1,C,D,hD,fun u hu ↦ he u hu.le⟩
  exact separate_regular_cube_identity e zero F G s t (fun k ↦ weaken (hf k))
    (fun k ↦ weaken (hg k)) apart repr

namespace Physical.JetExpression
/-- Evaluate the expression on arbitrary jet values. This distinguishes a
symbolic representation of a polynomial from equality on one solution. -/
def onJets (x : ℝ) (v : ℕ → ℂ) : JetExpression → ℂ
  | .coeff a => a.value x
  | .jet j => v j
  | .add a b => onJets x v a + onJets x v b
  | .mul a b => onJets x v a * onJets x v b

theorem on_regular (e : JetExpression) (x : ℝ) :
    e.onJets x (fun j ↦ iteratedDeriv j regularCube x) = e.evalRegular x := by
  induction e with
  | coeff | jet => rfl
  | add a b ha hb | mul a b ha hb => simp [onJets,evalRegular,ha,hb]

theorem represent_polynomial {J : ℕ} (P : MvPolynomial (Fin J) ℂ) :
    ∃ e : JetExpression, e.Admissible ∧ ∀ x v, e.onJets x v = MvPolynomial.eval (fun i : Fin J ↦ v i) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    let a : RayCoefficient := ⟨fun _ ↦ c,‖c‖,0,norm_nonneg _,by simp⟩
    exact ⟨.coeff a,TwoParities.of_integer (PowerClass.const c),by simp [onJets,a]⟩
  | add P Q hP hQ =>
    obtain ⟨e,he,hp⟩ := hP; obtain ⟨f,hf,hq⟩ := hQ
    exact ⟨.add e f,⟨he,hf⟩,by simp [onJets,hp,hq]⟩
  | mul_X P i hP =>
    obtain ⟨e,he,hp⟩ := hP
    exact ⟨.mul e (.jet i),⟨he,trivial⟩,by simp [onJets,hp]⟩
end Physical.JetExpression

/-- A polynomial identity in actual derivatives gives zero at every action
of a symbolically faithful expansion. No summability or kernel data are inputs. -/
theorem separate_regular_cube_polynomial {J : ℕ} (P : MvPolynomial (Fin J) ℂ)
    (zero : ∀ᶠ x : ℝ in atTop, MvPolynomial.eval
      (fun i : Fin J ↦ iteratedDeriv i.val Physical.regularCube x) P = 0) :
    ∃ e : Physical.JetExpression, (∀ x v, e.onJets x v = MvPolynomial.eval (fun i : Fin J ↦ v i) P) ∧
      ∀ n (j : e.withBackground.Frequency n), ∀ᶠ x : ℝ in atTop,
        e.withBackground.expansion.groupAmplitude e.withBackground.group ⟨n,j⟩ x = 0 := by
  obtain ⟨e,he,repr⟩ := Physical.JetExpression.represent_polynomial P
  refine ⟨e,repr,separate_admissible_regular_cube e he ?_⟩
  filter_upwards [zero] with x h
  rwa [← e.on_regular,repr]

/-- The positive-ray regularized cube series has no nonzero autonomous
polynomial relation among any finite number of its actual derivatives. -/
theorem regular_cube_no_autonomous_ade {J : ℕ} (P : MvPolynomial (Fin J) ℂ)
    (zero : ∀ᶠ x : ℝ in atTop, MvPolynomial.eval
      (fun i : Fin J ↦ iteratedDeriv i.val Physical.regularCube x) P = 0) : P = 0 := by
  let f (i : Fin J) := Physical.markedJet i.val
  have encode (Q : MvPolynomial (Fin J) ℂ) : ∃ e : Physical.JetExpression,
      e.Admissible ∧ (∀ x v, e.onJets x v = MvPolynomial.eval (fun i : Fin J ↦ v i) Q) ∧
      e.withBackground.marked = MvPolynomial.aeval f Q := by
    induction Q using MvPolynomial.induction_on with
    | C c =>
      let a : Physical.RayCoefficient := ⟨fun _ ↦ c,‖c‖,0,norm_nonneg _,by simp⟩
      refine ⟨.coeff a,TwoParities.of_integer (PowerClass.const c),by simp [Physical.JetExpression.onJets,a],?_⟩
      change (Physical.JetExpression.coeff a).marked = _
      rw [Physical.JetExpression.marked_coeff,MvPolynomial.aeval_C,MvPowerSeries.algebraMap_apply]; rfl
    | add A B ha hb =>
      obtain ⟨a,ha,ea,ma⟩ := ha; obtain ⟨b,hb,eb,mb⟩ := hb
      refine ⟨.add a b,⟨ha,hb⟩,by simp [Physical.JetExpression.onJets,ea,eb],?_⟩
      simp [Physical.JetExpression.withBackground,Physical.JetExpression.marked_add,ma,mb]
    | mul_X A i ha =>
      obtain ⟨a,ha,ea,ma⟩ := ha
      refine ⟨.mul a (.jet i),⟨ha,trivial⟩,by simp [Physical.JetExpression.onJets,ea],?_⟩
      change (a.withBackground.mul (Physical.JetExpression.jet i).withBackground).marked = _
      rw [Physical.JetExpression.marked_mul,ma,map_mul,MvPolynomial.aeval_X]; rfl
  obtain ⟨e,he,repr,marked⟩ := encode P
  have z := separate_admissible_regular_cube e he (by
    filter_upwards [zero] with x hx; rwa [← e.on_regular,repr])
  exact algebraicIndependent_iff.mp (Physical.independent_marked_jets J) P
    (marked.symm.trans (e.withBackground.marked_zero z))

/-- Pak's Conjecture 2.6 in the formal power series ring over ℂ.
Coordinate zero is X. Coordinate j+1 is the jth ordinary formal derivative
of the series with coefficient one at the nonnegative cubes and zero elsewhere.
Injectivity excludes coefficients rational in X after clearing denominators. -/
theorem pak_conjecture_2_6 : AlgebraicIndependent ℂ Nome.coordinates := by
  apply algebraicIndependent_iff.mpr
  intro Q zero
  by_contra nonzero
  obtain ⟨_,P,hP,hz⟩ := Nome.pak_formal_transfer Q nonzero zero
  exact hP (regular_cube_no_autonomous_ade P hz)

/-- Once infinitely many isolated waves have been obtained, the normalized
linearized identities force the characteristic polynomial to be zero. -/
theorem characteristic_zero {ι : Type*} (w : ι → ℂ) (hinf : (Set.range w).Infinite)
    (P : Polynomial ℂ) (J : Finset ℕ) (hs : P.support ⊆ J) (c : ℕ → ℝ → ℂ) (jet : ι → ℕ → ℝ → ℂ)
    (hc : ∀ j ∈ J, Tendsto (c j) atTop (𝓝 (P.coeff j)))
    (hj : ∀ p j, Tendsto (jet p j) atTop (𝓝 (w p ^ j)))
    (hzero : ∀ p, ∀ᶠ x : ℝ in atTop, ∑ j ∈ J, c j x * jet p j x = 0) : P = 0 := by
  apply P.eq_zero_of_infinite_isRoot
  apply hinf.mono
  rintro _ ⟨p,rfl⟩
  have hlim := tendsto_finsetSum J (fun j hj' ↦ (hc j hj').mul (hj p j))
  have hz : Tendsto (fun x : ℝ ↦ ∑ j ∈ J, c j x * jet p j x) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((hzero p).mono fun _ h ↦ h.symm)
  have he := tendsto_nhds_unique hlim hz
  change P.eval (w p) = 0
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine (Finset.sum_subset hs ?_).trans he
  intro j _ hn
  simp [Polynomial.notMem_support_iff.mp hn]

end CubicTheta
