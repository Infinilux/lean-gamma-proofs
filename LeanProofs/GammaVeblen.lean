/-
Γ₀ 在二元 Veblen 函数下的封闭性。

目标定理（`Ordinal.veblen_lt_gamma_zero`，另有字面形式 `gamma_zero_closed_under_veblen`）：

    a < Γ₀ → b < Γ₀ → veblen a b < Γ₀

核实结果：本仓库 Mathlib 里 `veblen` 只在 `Mathlib/SetTheory/Ordinal/Veblen.lean` 出现
（全库 grep 无其他引用），该文件关于 Γ₀ 只有 `veblen_gamma_zero`、`gamma_zero_eq_nfp`、
`gamma_zero_le_of_veblen_le`、`lt_gamma_zero`、`iterate_veblen_lt_gamma_zero`，
不存在「Γ₀ 对 `veblen` 封闭」的陈述，所以这里不是重复劳动。

两条独立证明路线：
1. `veblen_lt_gamma_zero`（主定理）：走「Γ₀ 是 `veblen · 0` 的不动点 + 字典序比较
   `veblen_lt_veblen_iff`」。顺带给出抽象版本 `veblen_lt_of_fixed`（`veblen · 0` 的任意
   不动点都对二元 `veblen` 封闭）与推广版本 `veblen_lt_gamma`（每个 `Γ_ o` 都封闭）。
2. `veblen_lt_gamma_zero_of_lt_iterate` / `..._of_lt_iterate'`：走任务书草拟的
   `lt_gamma_zero` 有限迭代高度路线，结论同样是目标定理。

无 `sorry`、无 `native_decide`、无自定义 `axiom`。
-/

import Mathlib.SetTheory.Ordinal.Veblen

noncomputable section

namespace Ordinal

variable {a b o γ : Ordinal}

/-! ### 热身引理 -/

/-- 二元 Veblen 项被对角线项控制：`veblen a b ≤ veblen (max a b) (max a b)`。
同时用到左右两个方向的单调性。 -/
theorem veblen_le_veblen_max : veblen a b ≤ veblen (max a b) (max a b) :=
  veblen_left_monotone b (le_max_left a b) |>.trans
    ((veblen_right_strictMono (max a b)).monotone (le_max_right a b))

/-- 迭代值 `ξ ↦ veblen ξ 0` 从任一起点出发都不下降（只用 `o ≤ veblen o 0`）。 -/
theorem le_iterate_veblen_zero {x : Ordinal} (n : ℕ) : x ≤ (fun a ↦ veblen a 0)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (left_le_veblen _ 0)

/-- 迭代高度越大，`(fun a ↦ veblen a 0)^[n] 0` 越大。 -/
theorem iterate_veblen_zero_le {m n : ℕ} (h : m ≤ n) :
    (fun a ↦ veblen a 0)^[m] 0 ≤ (fun a ↦ veblen a 0)^[n] 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have H : (fun a ↦ veblen a 0)^[m] 0 ≤
      (fun a ↦ veblen a 0)^[m] ((fun a ↦ veblen a 0)^[k] 0) :=
    isNormal_veblen_zero.monotone.iterate m zero_le
  rwa [← Function.iterate_add_apply] at H

/-- 单变量封闭性（锚点）：`Γ₀` 在 `ξ ↦ veblen ξ 0` 下封闭，由 `lt_gamma_zero` 直接给出。 -/
theorem veblen_zero_lt_gamma_zero (h : a < Γ₀) : veblen a 0 < Γ₀ := by
  obtain ⟨n, hn⟩ := lt_gamma_zero.1 h
  have H2 : veblen ((fun x ↦ veblen x 0)^[n] 0) 0 < Γ₀ := by
    simpa only [Function.iterate_succ_apply'] using iterate_veblen_lt_gamma_zero (n + 1)
  exact (veblen_left_monotone 0 (le_of_lt hn)).trans_lt H2

/-! ### 路线 2：有限迭代高度（任务书草拟的路线） -/

/-- 关键一步：`a, b` 被同一个有限迭代值压住时，`veblen a b` 被**下一个**迭代值压住。
「`veblen γ γ` 这类项怎么被 `(veblen · 0)` 的有限迭代控制」——不需要 `ω` 次迭代，
字典序比较 `veblen_le_veblen_iff` 直接给出一次跃迁 `veblen a b ≤ veblen γ 0`。 -/
theorem veblen_le_iterate_succ_veblen_zero {n : ℕ}
    (ha : a < (fun x ↦ veblen x 0)^[n] 0) (hb : b < (fun x ↦ veblen x 0)^[n] 0) :
    veblen a b ≤ (fun x ↦ veblen x 0)^[n + 1] 0 := by
  have H : veblen a b ≤ veblen ((fun x ↦ veblen x 0)^[n] 0) 0 :=
    veblen_le_veblen_iff.2 (Or.inr (Or.inl
      ⟨ha, le_trans (le_of_lt hb) (left_le_veblen _ 0)⟩))
  rw [Function.iterate_succ_apply']
  exact H

/-- 路线 2 的主定理：假设 strengthened 成有限的迭代高度。 -/
theorem veblen_lt_gamma_zero_of_lt_iterate {n : ℕ}
    (ha : a < (fun x ↦ veblen x 0)^[n] 0) (hb : b < (fun x ↦ veblen x 0)^[n] 0) :
    veblen a b < Γ₀ :=
  (veblen_le_iterate_succ_veblen_zero ha hb).trans_lt (iterate_veblen_lt_gamma_zero (n + 1))

/-- 路线 2 下目标定理的完整证明：先把 `a, b` 压进同一个迭代值 `max n m`。 -/
theorem veblen_lt_gamma_zero_of_lt_iterate' (ha : a < Γ₀) (hb : b < Γ₀) : veblen a b < Γ₀ := by
  obtain ⟨n, hn⟩ := lt_gamma_zero.1 ha
  obtain ⟨m, hm⟩ := lt_gamma_zero.1 hb
  refine veblen_lt_gamma_zero_of_lt_iterate (n := max n m) ?_ ?_
  · exact lt_of_lt_of_le hn (iterate_veblen_zero_le (Nat.le_max_left n m))
  · exact lt_of_lt_of_le hm (iterate_veblen_zero_le (Nat.le_max_right n m))

/-! ### 路线 1：不动点 + 字典序比较（主证明） -/

/-- 核心引理：`veblen · 0` 的**任意**不动点都对二元 `veblen` 封闭。
证明只用字典序比较 `veblen_lt_veblen_iff` 的中间分支：取 `o₁ = a`、`o₂ = γ`，
`a < γ` 与 `b < γ = veblen γ 0` 恰好命中该分支。 -/
theorem veblen_lt_of_fixed (hg : veblen γ 0 = γ) (ha : a < γ) (hb : b < γ) :
    veblen a b < γ := by
  rw [← hg]
  exact veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨ha, by rwa [hg]⟩))

/-- 每个 gamma 序数 `Γ_ o` 都对二元 Veblen 封闭（因为 `veblen (Γ_ o) 0 = Γ_ o`）。 -/
theorem veblen_lt_gamma (ha : a < Γ_ o) (hb : b < Γ_ o) : veblen a b < Γ_ o :=
  veblen_lt_of_fixed (veblen_gamma_zero o) ha hb

/-- **目标定理**：`Γ₀` 在二元 Veblen 函数下封闭。 -/
theorem veblen_lt_gamma_zero (ha : a < Γ₀) (hb : b < Γ₀) : veblen a b < Γ₀ :=
  veblen_lt_gamma ha hb

/-- 集合语言的重述：`Set.Iio Γ₀` 对 `veblen` 封闭。 -/
theorem veblen_mem_Iio_gamma_zero (ha : a ∈ Set.Iio (Γ₀ : Ordinal))
    (hb : b ∈ Set.Iio Γ₀) : veblen a b ∈ Set.Iio Γ₀ :=
  veblen_lt_gamma_zero ha hb

end Ordinal

open Ordinal

/-- 目标定理的字面形式（curried、不依赖 `Ordinal` 命名空间前缀），独立复核。 -/
theorem gamma_zero_closed_under_veblen :
    ∀ a b : Ordinal, a < Γ₀ → b < Γ₀ → veblen a b < Γ₀ :=
  fun _ _ ha hb => veblen_lt_gamma_zero ha hb

/-! ### 非空转检查：假设可满足，且定理能实例化到具体序数 -/

#check @Ordinal.veblen_lt_gamma_zero

/-- `ω < Γ₀`，所以定理的前提不是永假条件。 -/
theorem omega_lt_gamma_zero : ω < Γ₀ := omega0_lt_gamma 0

/-- 具体实例：`φ ω ω < Γ₀`（一个真正的二元 Veblen 项）。 -/
theorem veblen_omega_omega_lt_gamma_zero : veblen ω ω < Γ₀ :=
  veblen_lt_gamma_zero omega_lt_gamma_zero omega_lt_gamma_zero

/-- 具体实例：`φ ε₀ ε₀ < Γ₀`。 -/
theorem veblen_epsilon_zero_epsilon_zero_lt_gamma_zero : veblen ε₀ ε₀ < Γ₀ :=
  veblen_lt_gamma_zero (epsilon_zero_lt_gamma 0) (epsilon_zero_lt_gamma 0)

#print axioms Ordinal.veblen_le_veblen_max
#print axioms Ordinal.le_iterate_veblen_zero
#print axioms Ordinal.iterate_veblen_zero_le
#print axioms Ordinal.veblen_zero_lt_gamma_zero
#print axioms Ordinal.veblen_le_iterate_succ_veblen_zero
#print axioms Ordinal.veblen_lt_gamma_zero_of_lt_iterate
#print axioms Ordinal.veblen_lt_gamma_zero_of_lt_iterate'
#print axioms Ordinal.veblen_lt_of_fixed
#print axioms Ordinal.veblen_lt_gamma
#print axioms Ordinal.veblen_lt_gamma_zero
#print axioms Ordinal.veblen_mem_Iio_gamma_zero
#print axioms gamma_zero_closed_under_veblen
#print axioms omega_lt_gamma_zero
#print axioms veblen_omega_omega_lt_gamma_zero
#print axioms veblen_epsilon_zero_epsilon_zero_lt_gamma_zero
