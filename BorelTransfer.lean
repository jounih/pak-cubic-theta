module

public import DirectionalLaplace

/-! A differential polynomial in directional Laplace sums has a single Borel
residual on the common star domain. Flatness in one direction detects the
zero residual, hence gives an exact identity in other directions. -/
public section
namespace CubicTheta
open Set Complex MeasureTheory Filter
open scoped Topology
noncomputable section

structure Minor where
  atom : ℂ
  density : ℂ → ℂ

namespace Minor

def pull (d : ℂ) (F : ℂ → ℂ) (v : ℝ) := d * F (d*v)
def value (a : Minor) (d p : ℂ) := a.atom + complexLaplace (pull d a.density) (p*d)
def plus (a b : Minor) : Minor := ⟨a.atom + b.atom, fun z ↦ a.density z + b.density z⟩
def times (a b : Minor) : Minor := ⟨a.atom*b.atom, fun z ↦ a.atom*b.density z +
    b.atom*a.density z + complexConvolution a.density b.density z⟩
def jet (a : Minor) : Minor := ⟨0,fun z ↦ z*a.density z⟩

structure Domain (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  star : ∀ z ∈ U, ∀ t ∈ Icc (0:ℝ) 1, (t:ℂ)*z ∈ U

def ContainsRay (U : Set ℂ) (d : ℂ) := ∀ v : ℝ, 0 ≤ v → d*v ∈ U
def Good (a : Minor) (U : Set ℂ) (d : ℂ) :=
  AnalyticOnNhd ℂ a.density U ∧ ExpType (pull d a.density)

private theorem pull_conv (d : ℂ) (F G : ℂ → ℂ) :
    pull d (complexConvolution F G) = borelProduct (pull d F) (pull d G) := by
  funext v
  unfold pull
  rw [← complexConvolution_real (fun z ↦ d * F (d*z)) (fun z ↦ d * G (d*z)) v]
  unfold complexConvolution
  have eqn (t : ℝ) : d*F (d*((t:ℂ)*v)) * (d*G (d*((1-t:ℝ)*v))) =
      (d*d)*(F ((t:ℂ)*(d*v))*G ((1-t:ℝ)*(d*v))) := by
    rw [mul_left_comm d (t:ℂ),mul_left_comm d ((1-t:ℝ):ℂ)]; ring
  simp only [eqn,integral_const_mul]; ring

private theorem pull_plus (a b : Minor) (d : ℂ) :
    pull d (plus a b).density = fun v ↦ pull d a.density v + pull d b.density v := by
  funext v; simp [pull,plus,mul_add]

private theorem pull_times (a b : Minor) (d : ℂ) :
    pull d (times a b).density = fun v ↦ a.atom * pull d b.density v +
      b.atom * pull d a.density v + borelProduct (pull d a.density) (pull d b.density) v := by
  rw [← pull_conv]; funext v; simp only [pull,times]; ring

private theorem pull_jet (a : Minor) (d : ℂ) :
    pull d a.jet.density = fun v : ℝ ↦ d*((v:ℂ)*pull d a.density v) := by
  funext v; simp only [pull,jet]; ring

theorem Good.plus {a b : Minor} {U d} (ha : a.Good U d) (hb : b.Good U d) :
    (a.plus b).Good U d := ⟨ha.1.add hb.1,by rw [pull_plus]; exact ha.2.add hb.2⟩

theorem Good.times {a b : Minor} {U d} (hU : Domain U) (ha : a.Good U d) (hb : b.Good U d) :
    (a.times b).Good U d := by
  refine ⟨((analyticOnNhd_const.mul hb.1).add (analyticOnNhd_const.mul ha.1)).add
    (complexConvolution_analytic hU.isOpen hU.star ha.1 hb.1),?_⟩
  rw [pull_times]; exact ((hb.2.scale _).add (ha.2.scale _)).add (ha.2.convolution hb.2)

theorem Good.jet {a : Minor} {U d} (ha : a.Good U d) : a.jet.Good U d :=
  ⟨analyticOnNhd_id.mul ha.1,by rw [pull_jet]; exact ha.2.times_u.scale d⟩

private theorem pull_cont {a : Minor} {U d} (ray : ContainsRay U d) (ha : a.Good U d) :
    ContinuousOn (pull d a.density) (Ioi 0) :=
  continuousOn_const.mul (ha.1.continuousOn.comp (by fun_prop : Continuous
    (fun v : ℝ ↦ d*v)).continuousOn (fun v hv ↦ ray v hv.le))

/-- The filter of right half-planes in the rotated frequency. -/
def far (d : ℂ) : Filter ℂ := comap (fun p : ℂ ↦ (p*d).re) atTop

private theorem eventually_bound (d : ℂ) (R : ℝ) : ∀ᶠ p in far d, R < (p*d).re :=
  tendsto_comap.eventually (eventually_gt_atTop R)

private theorem Good.integrable {a : Minor} {U d} (ray : ContainsRay U d) (ha : a.Good U d) :
    ∀ᶠ p in far d, IntegrableOn (damped (p*d) (pull d a.density)) (Ioi 0) := by
  obtain ⟨_,D,_,_,hg⟩ := ha.2
  filter_upwards [eventually_bound d D] with p hp
  exact damped_integrable (pull_cont ray ha) hg hp

private theorem lap_add {F G : ℝ → ℂ} {p : ℂ}
    (hf : IntegrableOn (damped p F) (Ioi 0)) (hg : IntegrableOn (damped p G) (Ioi 0)) :
    complexLaplace (fun u ↦ F u + G u) p = complexLaplace F p + complexLaplace G p := by
  simpa only [complexLaplace,damped,mul_add] using! integral_add hf hg

private theorem lap_scale (F : ℝ → ℂ) (p c : ℂ) :
    complexLaplace (fun u ↦ c * F u) p = c * complexLaplace F p := by
  simp only [complexLaplace,damped,mul_left_comm _ c,integral_const_mul]

private theorem good_plus_value {a b : Minor} {U d} (ray : ContainsRay U d)
    (ha : a.Good U d) (hb : b.Good U d) :
    ∀ᶠ p in far d, (a.plus b).value d p = a.value d p + b.value d p := by
  filter_upwards [ha.integrable ray,hb.integrable ray] with p hp hq
  unfold value
  rw [pull_plus,lap_add hp hq]; change a.atom+b.atom+_ = _; ring

private theorem good_times_value {a b : Minor} {U d} (ray : ContainsRay U d)
    (hU : Domain U) (ha : a.Good U d) (hb : b.Good U d) :
    ∀ᶠ p in far d, (a.times b).value d p = a.value d p * b.value d p := by
  let l : Minor := ⟨0,fun z ↦ a.atom*b.density z⟩
  let r : Minor := ⟨0,fun z ↦ b.atom*a.density z⟩
  let k : Minor := ⟨0,complexConvolution a.density b.density⟩
  have eqL : pull d l.density = fun v ↦ a.atom * pull d b.density v := by funext v; simp [l,pull]; ring
  have eqR : pull d r.density = fun v ↦ b.atom * pull d a.density v := by funext v; simp [r,pull]; ring
  have hl : l.Good U d := ⟨analyticOnNhd_const.mul hb.1,by rw [eqL]; exact hb.2.scale _⟩
  have hr : r.Good U d := ⟨analyticOnNhd_const.mul ha.1,by rw [eqR]; exact ha.2.scale _⟩
  have hk : k.Good U d := ⟨complexConvolution_analytic hU.isOpen hU.star ha.1 hb.1,by
    change ExpType (pull d (complexConvolution _ _)); rw [pull_conv]; exact ha.2.convolution hb.2⟩
  filter_upwards [good_plus_value ray (hl.plus hr) hk,good_plus_value ray hl hr,
      ha.integrable ray,hb.integrable ray] with p hsum hparts hi hj
  have e : (a.times b).value d p = a.atom*b.atom + ((l.plus r).plus k).value d p := by
    simp [value,times,plus,l,r,k]
  rw [e,hsum,hparts]
  simp only [value,eqL,eqR,lap_scale,k,pull_conv,complexLaplace_product hi hj,l,r]; ring

private theorem good_jet_derivative {a : Minor} {U d} (ray : ContainsRay U d) (ha : a.Good U d) :
    ∀ᶠ p in far d, HasDerivAt (a.value d) (-a.jet.value d p) p := by
  obtain ⟨C,D,_,_,hg⟩ := ha.2
  filter_upwards [eventually_bound d (D+1)] with p hp
  have h := ((complexLaplace_derivative (pull_cont ray ha) hg hp).comp p
    ((hasDerivAt_id p).mul_const d)).const_add a.atom
  unfold value
  rw [pull_jet,lap_scale]
  simpa only [jet,zero_add,mul_comm d,neg_mul,
    Function.comp_def,id_eq,one_mul] using! h

/-- Multiplication by the frequency converts the unnormalized integral back
to the Watson normalization. -/
private theorem real_value (a : Minor) {x : ℝ} (hx : 0 < x) :
    (x:ℂ) * (a.value 1 x - a.atom) = raySum (fun v : ℝ ↦ a.density v) x := by
  rw [raySum_eq_weighted _ hx]
  simp [value,complexLaplace,pull,damped,weighted,Complex.real_smul,Complex.ofReal_exp]

/-- A constant plus a Laplace integral of an analytic density cannot be flat
on the positive real ray unless both the constant and the full density vanish. -/
theorem zero_of_flat {a : Minor} {U} (conn : IsPreconnected U) (ray : ContainsRay U 1)
    (ha : a.Good U 1) (flat : ∀ n : ℕ, Tendsto (fun x : ℝ ↦ (x:ℂ)^n * a.value 1 x)
      atTop (𝓝 0)) : a.atom = 0 ∧ EqOn a.density 0 U := by
  have origin : (0:ℂ) ∈ U := by simpa using ray 0 le_rfl
  let F := fun u : ℝ ↦ a.density u
  have cont : ContinuousOn F (Ioi 0) := by simpa [F,pull,Function.comp_def] using (show ContinuousOn (fun v : ℝ ↦ 1*a.density (1*v)) (Ioi 0) from pull_cont ray ha)
  obtain ⟨C,D,_,hD,hg⟩ := ha.2
  have growth (u : ℝ) (hu : 0 < u) : ‖F u‖ ≤ C*Real.exp (D*u) := by
    simpa [F,pull] using hg u hu.le
  have lead (n : ℕ) (g : ℂ → ℂ) (hc : ContinuousAt g 0)
      (fac : ∀ᶠ z in 𝓝 (0:ℂ), a.density z = z^n * g z) :
      Tendsto (fun x : ℝ ↦ (x:ℂ)^n * raySum F x) atTop (𝓝 ((n.factorial:ℂ)*g 0)) := by
    have inc : Tendsto ((↑) : ℝ → ℂ) (𝓝 0) (𝓝 0) := by simpa using continuous_ofReal.tendsto 0
    have h := raySum_leading cont hD growth (g := fun v : ℝ ↦ g v) (n := n)
      (by exact hc.tendsto.comp inc) (by
        filter_upwards [inc.eventually fac] with u h; simpa [F,Complex.real_smul] using h)
    simpa [Complex.real_smul] using h
  have bounded := lead 0 a.density (ha.1 0 origin).continuousAt (.of_forall (by simp))
  have scale : Tendsto (fun x : ℝ ↦ ((x:ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  have van : Tendsto (fun x : ℝ ↦ a.value 1 x - a.atom) atTop (𝓝 0) := by
    apply (show Tendsto (fun x : ℝ ↦ ((x:ℂ)⁻¹)*raySum F x) atTop (𝓝 0) from
      by simpa using scale.mul bounded).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [show raySum F x = _ from (real_value a hx).symm, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hx.ne'),one_mul]
  have atom : a.atom = 0 := by
    have h := tendsto_nhds_unique (by simpa using (flat 0).sub_const a.atom :
      Tendsto (fun x : ℝ ↦ a.value 1 x - a.atom) atTop (𝓝 (-a.atom))) van
    simpa using h
  refine ⟨atom,ha.1.eqOn_zero_of_preconnected_of_eventuallyEq_zero conn origin ?_⟩
  by_contra hn
  obtain ⟨n,g,hg,hg0,hfac⟩ := (ha.1 0 origin).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hn
  have lim := lead n g hg.continuousAt (by simpa using hfac)
  have zeroLim : Tendsto (fun x : ℝ ↦ (x:ℂ)^n * raySum F x) atTop (𝓝 0) := by
    apply (flat (n+1)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [pow_succ,show raySum F x = _ from (real_value a hx).symm,atom,sub_zero,mul_assoc]
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) (tendsto_nhds_unique lim zeroLim)

end Minor

/-- The operations of a differential polynomial, with convergent coefficients
and the unknown series supplied as leaves. A jet denotes minus d/dp. -/
inductive BorelExpr (ι : Type*) where
  | leaf (i : ι)
  | add (e f : BorelExpr ι)
  | mul (e f : BorelExpr ι)
  | jet (e : BorelExpr ι)

namespace BorelExpr
open Minor
variable {ι : Type*}

def residual (a : ι → Minor) : BorelExpr ι → Minor
  | leaf i => a i
  | add e f => (e.residual a).plus (f.residual a)
  | mul e f => (e.residual a).times (f.residual a)
  | jet e => (e.residual a).jet

def eval (a : ι → Minor) (d : ℂ) : BorelExpr ι → ℂ → ℂ
  | leaf i => (a i).value d
  | add e f => fun p ↦ e.eval a d p + f.eval a d p
  | mul e f => fun p ↦ e.eval a d p * f.eval a d p
  | jet e => fun p ↦ -deriv (e.eval a d) p

theorem represents (e : BorelExpr ι) {U d} (hU : Domain U) (ray : ContainsRay U d)
    {a : ι → Minor} (ha : ∀ i, (a i).Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[far d] (e.residual a).value d := by
  induction e with
  | leaf i => exact ⟨ha i,.rfl⟩
  | add e f he hf =>
    refine ⟨he.1.plus hf.1,?_⟩
    filter_upwards [he.2,hf.2,good_plus_value ray he.1 hf.1] with p hp hq h
    simp only [residual,eval,h,hp,hq]
  | mul e f he hf =>
    refine ⟨he.1.times hU hf.1,?_⟩
    filter_upwards [he.2,hf.2,good_times_value ray hU he.1 hf.1] with p hp hq h
    simp only [residual,eval,h,hp,hq]
  | jet e he =>
    refine ⟨he.1.jet,?_⟩
    obtain ⟨R,hR⟩ := eventually_atTop.mp (eventually_comap.mp he.2)
    filter_upwards [eventually_bound d R,good_jet_derivative ray he.1] with p hp h
    have loc : e.eval a d =ᶠ[𝓝 p] (e.residual a).value d := by
      filter_upwards [(isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_id.mul_const d))).mem_nhds hp] with q hq
      exact hR _ (le_of_lt hq) q rfl
    simp only [eval,residual,loc.deriv_eq,h.deriv,neg_neg]

/-- An identity flat in the physical direction holds exactly on a target
half-plane. Apply this twice to get both lateral identities at the same p. -/
theorem transfer (e : BorelExpr ι) {U d} (hU : Domain U) (conn : IsPreconnected U)
    (phys : ContainsRay U 1) (target : ContainsRay U d) {a : ι → Minor}
    (hphys : ∀ i, (a i).Good U 1) (htar : ∀ i, (a i).Good U d)
    (flat : ∀ n : ℕ, Tendsto (fun x : ℝ ↦ (x:ℂ)^n * e.eval a 1 x) atTop (𝓝 0)) :
    ∀ᶠ p in far d, e.eval a d p = 0 := by
  obtain ⟨good,rep⟩ := e.represents hU phys hphys
  have inc : Tendsto ((↑) : ℝ → ℂ) atTop (far 1) := by
    apply tendsto_comap_iff.mpr
    change Tendsto (fun x : ℝ ↦ ((x:ℂ)*1).re) atTop atTop
    simp only [mul_one,Complex.ofReal_re]; exact tendsto_id
  obtain ⟨atom,density⟩ := zero_of_flat conn phys good (fun n ↦
    (flat n).congr' (by filter_upwards [inc.eventually rep] with x hx; rw [hx]))
  filter_upwards [(e.represents hU target htar).2] with p hp
  rw [hp,value,atom,zero_add]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro v hv
  simp [damped,pull,show (e.residual a).density (d*v) = 0 from density (target v hv.le)]

/-- Sufficient positivity puts both lateral evaluations on the same
extraction ray with one common lower bound on its radius. -/
theorem transfer_both_on_ray (e : BorelExpr ι) {U} (hU : Domain U) (conn : IsPreconnected U)
    {a : ι → Minor} (phys : ContainsRay U 1) (hphys : ∀ i, (a i).Good U 1)
    (flat : ∀ n : ℕ, Tendsto (fun x : ℝ ↦ (x:ℂ)^n * e.eval a 1 x) atTop (𝓝 0))
    (lo hi q : ℂ) (rlo : ContainsRay U lo) (rhi : ContainsRay U hi)
    (glo : ∀ i, (a i).Good U lo) (ghi : ∀ i, (a i).Good U hi)
    (plo : 0 < (q*lo).re) (phi : 0 < (q*hi).re) :
    ∀ᶠ x : ℝ in atTop, e.eval a lo (q*x) = 0 ∧ e.eval a hi (q*x) = 0 := by
  have go (d : ℂ) (hd : 0 < (q*d).re) : Tendsto (fun x : ℝ ↦ q*x) atTop (far d) := by
    apply tendsto_comap_iff.mpr
    change Tendsto (fun x : ℝ ↦ (q*x*d).re) atTop atTop
    simpa only [mul_right_comm q _ d,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero] using! (show Tendsto (fun x : ℝ ↦ (q*d).re*x) atTop atTop from
        tendsto_id.const_mul_atTop hd)
  exact ((go lo plo).eventually (transfer e hU conn phys rlo hphys glo flat)).and
    ((go hi phi).eventually (transfer e hU conn phys rhi hphys ghi flat))

end BorelExpr
end
end CubicTheta
