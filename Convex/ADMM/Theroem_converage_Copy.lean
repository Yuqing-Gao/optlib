import Convex.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences
import Convex.ADMM.Lemma_Copy
import Convex.ADMM.Scheme
import Convex.ADMM.Image_subgradient_closed
noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric


--列满秩等价于单射ker = 0
variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)
variable(fullrank₁: Function.Injective admm.A₁)(fullrank₂: Function.Injective admm.A₂)

namespace ADMM_Converage_Lemma_Proof

variable {admm admm_kkt}

local notation "f₁" => admm.f₁
local notation "f₂" => admm.f₂
local notation "A₁" => admm.A₁
local notation "A₂" => admm.A₂
local notation "b" => admm.b
local notation "x₁" => admm.x₁
local notation "x₂" => admm.x₂
local notation "y" => admm.y
local notation "τ" => admm.τ
local notation "ρ" => admm.ρ

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'" => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂

section

variable [Setting E₁ E₂ F admm admm_kkt]

lemma inSet {X : Type*} ( f : ℕ → X ) : ∀ n : ℕ , f n ∈ range f := by
   intro n;use n

--dyx xzx

lemma nonneg₁ : min τ (1 + τ - τ ^ 2) > 0 :=sorry
lemma nonneg₂ : min 1 (1 + 1 / τ - τ) > 0 :=sorry
lemma Φ_is_monotone : ∀ n : ℕ+, Φ n ≥ Φ (n+1) := by
   intro n
   let c := (min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
          + (min 1 (1 + 1 / τ - τ)) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2
   have h : c ≥ 0 := by
      sorry
   have h' : (Φ n) - (Φ (n + 1)) ≥ 0 := by
      calc
         _ ≥ c := by apply Φ_isdescending
         _ ≥ 0 := by apply h
   linarith [h']

lemma nonneg₃ : min (1 - τ) (1 - 1 / τ) > 0 :=sorry
lemma Φ_is_nonneg : ∀ n : ℕ , Φ n ≥ 0 := by sorry


--byf
--Φ 是有界序列
lemma Φ_isBounded' : ∃ (r : ℝ), (range Φ) ⊆ ball 0 r := by
   let c := Max.max ((Φ 0) + 1) ((Φ 1) + 1)
   have Φ_bd_above (n : ℕ): Φ n < c := by
      induction' n with k h
      ·  have : Φ 0 < (Φ 0) + 1 := by linarith
         apply lt_max_iff.2
         left; exact this
      ·  by_cases hh : k = 0
         ·  rw [hh,zero_add]
            apply lt_max_iff.2
            right; linarith
         ·  push_neg at hh
            have k_pos : k > 0 := by apply Nat.pos_of_ne_zero hh
            have : (Φ) (k.toPNat k_pos) ≥ (Φ) ((k.toPNat k_pos ) + 1) := by
               apply Φ_is_monotone
            have h' : Φ (k.toPNat k_pos) < c := by apply h
            show Φ ((k.toPNat k_pos) + 1) < c
            linarith
   use c; intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩; rw [← eq, abs_eq_self.2]; exact Φ_bd_above n
   apply Φ_is_nonneg

lemma Φ_isBounded : IsBounded (range Φ) := (isBounded_iff_subset_ball 0).2  Φ_isBounded'


--ey是有界序列
lemma ey_isBounded' : ∃ (r : ℝ), (range ey) ⊆ ball 0 r := sorry
lemma ey_isBounded : IsBounded (range ey ) := (isBounded_iff_subset_ball 0).2  ey_isBounded'

--gyq
--A₂e₂ 是有界序列
lemma unfold_Φ: ∀ n, ‖Φ n‖ = ‖1 / (τ*ρ) * ‖ey n‖ ^ 2
+ ρ * ‖A₂ (e₂ n)‖ ^ 2
+ max (1 - τ) (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2‖ := by
   unfold Φ Ψ
   simp

lemma tau_pos : 0 < τ := by apply ADMM.htau.1

lemma rho_pos : 0 < ρ := by exact ADMM.hrho

lemma zero_le_tau_mul_rho : 0 ≤ τ * ρ := by
   have h : 0 < τ * ρ := by exact mul_pos tau_pos rho_pos
   apply le_of_lt h

lemma max_tau_nonneg : 0 ≤ max (1 - τ) (1 - 1 / τ) := by
   have h1: 0 ≤ 1 - τ ∨ 0 ≤ 1 - 1 / τ := by
      by_cases h_tau_le_1 : τ ≤ 1
      left; linarith [h_tau_le_1]
      right
      have hτ_inv_pos : 1 / τ < 1 := by
         rw [not_le] at h_tau_le_1
         rw [← div_lt_one tau_pos] at h_tau_le_1
         exact h_tau_le_1
      linarith [hτ_inv_pos]

   rw [← le_max_iff] at h1
   exact h1

lemma ineq1: ∀ n, ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ := by
   intro n
   let x1 := 1 / (τ*ρ) * ‖ey n‖ ^ 2
   have hx1: 0 ≤ x1 := by
      apply mul_nonneg
      · apply div_nonneg
         zero_le_one; exact zero_le_tau_mul_rho
      · apply pow_nonneg; simp
   let x2 := ρ * ‖A₂ (e₂ n)‖ ^ 2
   have hx2: 0 ≤ x2 := by
      apply mul_nonneg
      · apply le_of_lt rho_pos
      · apply pow_nonneg; simp
   let x3 := max (1 - τ) (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2
   have hx3: 0 ≤ x3 := by
      apply mul_nonneg
      · apply mul_nonneg
         max_tau_nonneg; apply le_of_lt rho_pos
      · apply pow_nonneg; simp

   have h: ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ ↔ x2 ≤ ‖x1 + x2 + x3‖ := by rw[unfold_Φ]
   have h_norm_pos : 0 ≤ ‖x1 + x2 + x3‖ := by exact norm_nonneg (x1 + x2 + x3)
   have h_norm_eq : ‖x1 + x2 + x3‖ = x1 + x2 + x3 := by rw [Real.norm_of_nonneg];linarith [hx1, hx2, hx3]

   have htrans: x2 ≤ ‖x1 + x2 + x3‖ := by linarith [hx2, h_norm_pos]
   exact (h.mpr htrans)

lemma A₂e₂_isBounded' : ∃ (r : ℝ), (range (A₂ ∘ e₂) ) ⊆ ball 0 r := by

   have hΦ : ∃ r_Φ, range Φ ⊆ Metric.ball 0 r_Φ := by apply Φ_isBounded'
   rcases hΦ with ⟨r_Φ, hΦ⟩

   have h1 : ∀ n, ‖Φ n‖ < r_Φ := by
      intro n
      have h0 : Φ n ∈ range Φ := by use n
      have h_in_ball : Φ n ∈ Metric.ball 0 r_Φ := by
         apply hΦ h0
      rw [Metric.mem_ball, dist_zero_right] at h_in_ball
      exact h_in_ball

   let r := √ (r_Φ / ρ)
   have hr : r = √ (r_Φ / ρ) := by rfl
   use r
   intros x hx
   rcases hx with ⟨n, rfl⟩

   have h2 : ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ := by apply ineq1

   have h3 : ρ * ‖A₂ (e₂ n)‖ ^ 2 < r_Φ := by
      calc
      ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ := h2
      _ < r_Φ := h1 n

   have h4 : 0 ≤ ‖A₂ (e₂ n)‖ := by
      apply norm_nonneg

   have h5: ‖A₂ (e₂ n)‖ < √ (r_Φ / ρ) := by
      calc ‖A₂ (e₂ n)‖
         = √ ((‖A₂ (e₂ n)‖) ^ 2) := by conv in ‖A₂ (e₂ n)‖ => rw [← Real.sqrt_sq h4];rfl
         _ < √ (r_Φ / ρ) := by
            rw [← lt_div_iff' ADMM.hrho] at h3
            apply Real.sqrt_lt_sqrt at h3
            exact h3; simp

   have h6: dist (A₂ (e₂ n)) 0 < √ (r_Φ / ρ) := by
      rw[← sub_zero (A₂ (e₂ n))] at h5
      rw[SeminormedAddGroup.dist_eq (A₂ (e₂ n)) 0]
      exact h5

   rw [← hr] at h6
   rw [← Metric.mem_ball] at h6
   apply h6

--A₁e₁ + A₂e₂ 是有界序列
#check Φ_isdescending
#check Φ_isBounded'

lemma A₁e₁_A₂e₂_isBounded' : ∃ (r : ℝ), (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) ⊆ ball 0 r := by
   -- obtain r_Φ
   have hΦ : ∃ r_Φ, range Φ ⊆ Metric.ball 0 r_Φ := by apply Φ_isBounded'
   rcases hΦ with ⟨r_Φ, hΦ⟩
   -- obtain r
   let r := √ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ))
   have hr : r =√ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by rfl
   use r
   -- change goal, introduce n
   intros x hx
   rcases hx with ⟨n, rfl⟩
   #check n
   -- h1 ~ h5 : n ≥ 1 (n : ℕ +)
   have h1 : (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 ≤
   (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 +
   (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 := by sorry
   have h3 : (Φ n ) - (Φ (n + 1) ) < 2 * r_Φ := by sorry
   have h2 : (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 + (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 ≤ (Φ n ) - (Φ (n + 1) ) := by sorry
   have h4 : (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 < 2 * r_Φ := by
      calc (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2
         _ ≤ (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 + (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 := h1
         _ ≤ (Φ n ) - (Φ (n + 1) ) := h2
         _ < 2 * r_Φ := h3
   have h5 : ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ < √ (r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by sorry

   -- back to goal : n ≥ 0 (n : ℕ)
   have h5' : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < √ (r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by sorry

   have h6: dist (A₁ (e₁ n) + A₂ (e₂ n)) 0 < √ ( 2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by sorry

   rw [← hr] at h6; rw [← Metric.mem_ball] at h6; simp; simp at h6
   exact h6



lemma A₁e₁_A₂e₂_isBounded : IsBounded (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 A₁e₁_A₂e₂_isBounded'

--mht
--A₁e₁ 是有界序列
lemma A₁e₁_isBounded' : ∃ (r : ℝ), (range (A₁ ∘ e₁) ) ⊆ ball 0 r := sorry

lemma A₁e₁_isBounded : IsBounded (range (A₁ ∘ e₁) ) :=
   (isBounded_iff_subset_ball 0).2 A₁e₁_isBounded'

--byf
--x₁这个序列是有界的
lemma x₁_isBounded' : ∃ (r : ℝ), (range x₁) ⊆ ball 0 r := sorry
lemma x₁_isBounded [Setting E₁ E₂ F admm admm_kkt]:  IsBounded (range x₁) :=
   (isBounded_iff_subset_ball 0).2 x₁_isBounded'

--x₂这个序列是有界的
lemma x₂_isBounded' : ∃ (r : ℝ), (range x₂ ) ⊆ ball 0 r := sorry
lemma x₂_isBounded [Setting E₁ E₂ F admm admm_kkt]:  IsBounded (range x₂) :=
   (isBounded_iff_subset_ball 0).2 x₂_isBounded'

--y这个序列是有界的
lemma y_isBounded' :  ∃ (r : ℝ), (range y) ⊆ ball 0 r := sorry
lemma y_isBounded  [Setting E₁ E₂ F admm admm_kkt]:  IsBounded (range y) :=
   (isBounded_iff_subset_ball 0).2  y_isBounded'


lemma times_eq : (range (fun n => (x₁ n,  x₂ n, y n ) ))
⊆  (range x₁) ×ˢ  (range x₂) ×ˢ (range y) := by
   simp [range]
   intro x hx
   dsimp at hx
   simp only [mem_prod, mem_setOf_eq]
   rcases hx with ⟨n , hn⟩
   have h1 : x₁ n = x.1 := hn.symm ▸ rfl
   have h2 : x₂ n = x.2.1 := hn.symm ▸ rfl
   have h3 : y  n = x.2.2 := hn.symm ▸ rfl
   exact ⟨ ⟨ n , h1 ⟩, ⟨ n , h2 ⟩, ⟨ n , h3 ⟩⟩


lemma xy_isBounded : IsBounded (range (fun n => (x₁ n,  x₂ n, y n ) )) := by
   apply IsBounded.subset
   apply IsBounded.prod x₁_isBounded
   apply IsBounded.prod x₂_isBounded y_isBounded
   apply times_eq

--取出子列收敛
structure Converage_Subseq [Setting E₁ E₂ F admm admm_kkt] where
   x₁'' : E₁
   x₂'' : E₂
   y''  : F
   φ    : ℕ → ℕ
   hphi:StrictMono φ
   hconverage:Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n))) atTop (𝓝 (x₁'' , x₂'' , y''))

#check Converage_Subseq.mk
-- #check tendsto_subseq_of_bounded
-- #check tendsto_subseq_of_bounded (xy_isBounded admm) (inSet (fun n => (x₁ n,  x₂ n, y n )) )
-- #check Exists.choose $ tendsto_subseq_of_bounded (xy_isBounded admm) (inSet (fun n => (x₁ n,  x₂ n, y n )) )
-- #check Exists.choose_spec $ tendsto_subseq_of_bounded (xy_isBounded admm) (inSet (fun n => (x₁ n,  x₂ n, y n )) )
-- #check Exists.choose
--取出子列收敛
def Subseq : Converage_Subseq := by
   let x := tendsto_subseq_of_bounded xy_isBounded (inSet (fun n => (x₁ n,  x₂ n, y n )) )
   choose x hx using x
   choose φ hphi1 using hx.2
   exact
      {
         x₁'' := x.1
         x₂'' := x.2.1
         y''  := x.2.2
         φ   := φ
         hphi:= hphi1.1
         hconverage:=hphi1.2
      }

--子列映射
local notation "φ" => Subseq.φ

--子列收敛的点
local notation "x₁''" => Subseq.x₁''
local notation "x₂''" => Subseq.x₂''
local notation "y''" => Subseq.y''

--子列映射是严格单增
lemma hphi_StrictMono : StrictMono φ := Subseq.hphi


--子列映射是严格单增(x₁ (φ n),  x₂ (φ n), y (φ n))) atTop (nhds (x₁' , x₂' , y'))
--子列收敛
--lim_{n → ∞} (uₙ ,vₙ ) = 0 -> lim_{n → ∞} uₙ  = 0


#check nhds_prod_eq
lemma admm_nhds_prod_eq : 𝓝 (x₁'' , x₂'' , y'') = 𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y'' := by
   rw[nhds_prod_eq,nhds_prod_eq]

lemma hconverage : Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n)))
atTop (𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y''):=by
   have := Subseq.hconverage
   rw[admm_nhds_prod_eq] at this
   exact this


#check Filter.tendsto_prod_iff'.1 (hconverage)
lemma x₁_subseq_converage : Tendsto (fun n => (x₁ (φ n)))  atTop (𝓝 x₁'') :=
   (Filter.tendsto_prod_iff'.1 hconverage).1
lemma x₂_subseq_converage : Tendsto (fun n => (x₂ (φ n)))  atTop (𝓝 x₂'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 hconverage).2).1
lemma y_subseq_converage  : Tendsto (fun n => (y (φ n)))  atTop (𝓝 y'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 hconverage).2).2

def φ₁ : ℕ → ℕ+ := by
   intro n
   exact (φ (n + 1)).toPNat'

#check StrictMono.id_le (hphi_StrictMono)
lemma φ₁_equ : ∀ n , φ₁ n = φ (n + 1) := by
   intro n
   have : φ (n + 1) > 0 := by
      calc φ (n + 1)
         _ ≥ n + 1  := StrictMono.id_le hphi_StrictMono (n + 1)
         _ > 0      :=by linarith
   exact Nat.sub_one_add_one_eq_of_pos this
    --only [Nat.toPNat'_coe, this, ↓reduceIte]

-- lim_{ n → ∞} x_n  = x =>  lim_{ n → ∞} x_{n+1}  = x
#check Filter.tendsto_add_atTop_iff_nat
lemma x₁_subseq_converage' : Tendsto (fun n => (x₁ (φ₁ n)))  atTop (𝓝 x₁'') :=by
   have : (fun n => x₁ (φ₁ n)) = (fun n => (x₁ (φ (n+1)))) :=by ext n;rw[φ₁_equ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₁ (φ n)) ) 1]
   apply x₁_subseq_converage

lemma x₂_subseq_converage' : Tendsto (fun n => (x₂ (φ₁ n)))  atTop (𝓝 x₂'') :=by
   have : (fun n => x₂ (φ₁ n)) = (fun n => (x₂ (φ (n+1)))) :=by ext n;rw[φ₁_equ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₂ (φ n)) ) 1]
   apply x₂_subseq_converage
#check summable_of_sum_range_le
--可和
lemma Summable₁' :∃ (c : ℝ) , ∀ (n : ℕ), ∑ i ∈ Finset.range n, ‖A₁ (e₁ i) + A₂ (e₂ i)‖^2 ≤ c := by
   sorry

lemma Summable₁ : Summable (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖^2) :=by
   rcases Summable₁'  with ⟨c , hn⟩
   apply summable_of_sum_range_le (c:=c)
   intro n
   apply zpow_two_nonneg
   exact hn

lemma Summable₂' [Setting E₁ E₂ F admm admm_kkt] :∃ (c : ℝ) ,
   ∀ (n : ℕ), ∑ i ∈ Finset.range n,  ‖A₂ (x₂ (i+1) - x₂ i)‖^2 ≤ c := by sorry

lemma Summable₂ : Summable (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖^2) :=by
   rcases Summable₂'  with ⟨c , hn⟩
   apply summable_of_sum_range_le (c:=c)
   intro n
   apply zpow_two_nonneg
   exact hn

#check Summable.tendsto_atTop_zero

--几个范数收敛于0
lemma converage_zero₁ : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖)  atTop (𝓝 0) := sorry
lemma converage_zero₂ : Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - admm.b‖)  atTop (𝓝 0) := sorry
lemma converage_zero₃ : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := sorry

-- #check (A₁)†

lemma u_subseq_converage : Tendsto (fun n => u (φ₁ n)) atTop
(𝓝 (- A₁† y'')) := sorry

lemma v_subseq_converage : Tendsto (fun n => v (φ₁ n)) atTop
(𝓝 (- A₂† y'')) := sorry

#check u_inthesubgradient
lemma A₁'y_inthesubgradient : - A₁† y'' ∈ SubderivAt f₁ x₁'':=
   Image_subgradient_closed f₁ x₁'' (- A₁† y'')
   admm.lscf₁ admm.cf₁  (fun n => x₁ (φ₁ n))
   x₁_subseq_converage' (fun n => u  (φ₁ n))
   u_subseq_converage   (fun n => u_inthesubgradient (φ₁ n))

lemma A₂'y_inthesubgradient : - A₂† y'' ∈ SubderivAt f₂ x₂'':=
   Image_subgradient_closed f₂ x₂'' (- A₂† y'')
   admm.lscf₂ admm.cf₂  (fun n => x₂ (φ₁ n))
   x₂_subseq_converage' (fun n => v  (φ₁ n))
   v_subseq_converage   (fun n => v_inthesubgradient (φ₁ n))

lemma Satisfying_equational_constraint : (A₁ x₁'') + (A₂ x₂'') = admm.b:=sorry

lemma Iskktpair : Convex_KKT x₁'' x₂'' y'' admm.toOpt_problem :=
   {
      subgrad₁ :=A₁'y_inthesubgradient
      subgrad₂ :=A₂'y_inthesubgradient
      eq       :=Satisfying_equational_constraint
   }



lemma A₁e₁_converage_zero : Tendsto (fun n => ‖(A₁ ∘ e₁) n‖) atTop (𝓝 0) :=sorry

end

--子列映射
local notation "φ" => Subseq.φ

--子列收敛的点
local notation "x₁''" => Subseq.x₁''
local notation "x₂''" => Subseq.x₂''
local notation "y''" => Subseq.y''

def admm_kkt₁ [s : Setting E₁ E₂ F admm admm_kkt] :  Existance_of_kkt admm :=
   Existance_of_kkt.mk x₁''  x₂''  y'' Iskktpair

variable [Setting E₁ E₂ F admm (admm_kkt₁ (admm_kkt := admm_kkt) (s := ⟨⟩))]

#check e₁
lemma e₁_subseq_converage_zero : Tendsto (e₁ ∘ φ) atTop (𝓝 0) :=sorry
lemma e₂_subseq_converage_zero : Tendsto (e₂ ∘ φ) atTop (𝓝 0) :=sorry
lemma ey_subseq_converage_zero : Tendsto (ey ∘ φ) atTop (𝓝 0) :=sorry

#check Φ
#check  tendsto_zero_iff_norm_tendsto_zero
lemma Φ_subseq_converage_zero : Tendsto (fun n => Φ (φ n)) atTop (𝓝 0) := sorry
lemma Φ_converage_zero : Tendsto Φ atTop (𝓝 0) := sorry


lemma e₁_converage_zero : Tendsto e₁ atTop (𝓝 0) :=sorry
lemma e₂_converage_zero : Tendsto e₂ atTop (𝓝 0) :=sorry
lemma ey_converage_zero : Tendsto ey atTop (𝓝 0) :=sorry

#check e₁
--lim_{ n → ∞} x_n - x = 0 =>  lim_{ n → ∞} x_n  = x
#check tendsto_sub_nhds_zero_iff
lemma x₁_converage : Tendsto x₁ atTop (𝓝 x₁'') := by
   have : e₁ = (fun n => (x₁ n) - x₁''):= rfl
   have h := e₁_converage_zero
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma x₂_converage : Tendsto x₂ atTop (𝓝 x₂'') := by
   have : e₂ = (fun n => (x₂ n) - x₂''):= rfl
   have h := e₂_converage_zero
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma y_converage : Tendsto y atTop (𝓝 y'') := by
   have : ey = (fun n => (y n) - y''):= rfl
   have h := ey_converage_zero
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h


--ADMM收敛定理
theorem ADMM_convergence :  ∃ ( _x₁   : E₁) ( _x₂ : E₂) ( _y : F) ,
Convex_KKT _x₁ _x₂ _y admm.toOpt_problem
∧ ( Tendsto x₁ atTop (𝓝 _x₁)∧ Tendsto x₂ atTop (𝓝 _x₂)∧ Tendsto y atTop (𝓝 _y)) :=
   ⟨x₁'',x₂'',y'',Iskktpair ,x₁_converage ,x₂_converage ,y_converage ⟩

end ADMM_Converage_Lemma_Proof
