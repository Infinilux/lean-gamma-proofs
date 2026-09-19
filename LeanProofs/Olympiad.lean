import Mathlib

/-!
# 六条竞赛风格定理的完整 Lean 证明

没有 `sorry`、没有 `native_decide`、没有自定义 `axiom`；`#print axioms` 只列出
`propext, Classical.choice, Quot.sound`（CI 里逐条核对）。

| 名称 | 陈述 | 关键手法 |
| --- | --- | --- |
| `hm_am3` | `x,y,z>0 ⟹ (1/x+1/y+1/z)(x+y+z) ≥ 9` | 恒等式 `(xy+yz+zx)(x+y+z) − 9xyz = Σ x(y−z)²`，`ring` 验证 + `positivity` |
| `nesbitt` | **Nesbitt** `a/(b+c)+b/(c+a)+c/(a+b) ≥ 3/2` | 代换 `x=b+c, y=c+a, z=a+b` 化归到 `hm_am3` |
| `cauchy_schwarz_two` | `(ac+bd)² ≤ (a²+b²)(c²+d²)` | 一行 `nlinarith [sq_nonneg (ad−bc)]`（Lagrange 恒等式） |
| `pow_five_mod_thirty` | `n⁵ ≡ n [MOD 30]` | 在 `ZMod 30` 上用核内 `decide` 判定 30 个情形，再经 `ZMod.natCast_eq_natCast_iff` 拉回 |
| `sum_cubes` | `4·Σ_{i≤n} i³ = (n(n+1))²` | 对 `n` 归纳，`Finset.sum_range_succ` + `ring` |
| `amgm_one` | `a,b,c>0, abc=1 ⟹ a+b+c ≥ 3` | `Real.geom_mean_le_arith_mean3_weighted` + `Real.mul_rpow` |

## 与 Mathlib 的关系

这些都不是新结果，是教科书不等式/恒等式的具体形式。核实过的事：在本仓库
Mathlib 快照里全库 grep `nesbitt`（大小写不敏感）、`∑ i in range _, i ^ 3`、
`n ^ 5 ≡` 均无命中，所以这几条陈述形式没有现成版本；但证明里用的原料
（加权 AM–GM、`ZMod`、`Finset` 求和、`nlinarith`/`positivity`）全部来自
Mathlib，没有任何重造轮子的企图。价值在于「能把题目变成编译通过的 Lean」，
不在于题目本身。
-/

noncomputable section

namespace LeanProofs

open BigOperators Finset

namespace Olympiad

/-- **三元 HM–AM 不等式**：`(1/x+1/y+1/z)(x+y+z) ≥ 9`。
全部代数内容集中在这条恒等式上：
`(xy+yz+zx)(x+y+z) − 9xyz = x(y−z)² + y(z−x)² + z(x−y)²`，由 `ring` 验证，
右边由 `positivity` 判非负。 -/
theorem hm_am3 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (1 / x + 1 / y + 1 / z) * (x + y + z) ≥ 9 := by
  have h₀ : 0 < x * y * z := by positivity
  have h1 : (1 / x + 1 / y + 1 / z) * (x + y + z)
      = (x * y + y * z + z * x) * (x + y + z) / (x * y * z) := by
    field_simp
    ring
  have hD : (x * y + y * z + z * x) * (x + y + z) - 9 * (x * y * z)
      = x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by ring
  have hge : 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by positivity
  have h9 : (9 : ℝ) * (x * y * z) ≤ (x * y + y * z + z * x) * (x + y + z) := by
    rw [← sub_nonneg, hD]
    exact hge
  rw [h1]
  refine ((le_div_iff₀ h₀).mpr ?_)
  exact h9

/-- **Nesbitt 不等式**：`a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2`。
代换 `x = b+c, y = c+a, z = a+b` 给出 `a = (y+z−x)/2`，于是左边等于
`(1/2)(x+y+z)(1/x+1/y+1/z) − 3`，由 `hm_am3` 下界为 `9/2 − 3`。 -/
theorem nesbitt {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h₁ : 0 < b + c := add_pos hb hc
  have h₂ : 0 < c + a := add_pos hc ha
  have h₃ : 0 < a + b := add_pos ha hb
  have key := hm_am3 h₁ h₂ h₃
  have h₄ : a / (b + c) + b / (c + a) + c / (a + b)
      = (1 / 2) * ((b + c + (c + a) + (a + b))
        * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))) - 3 := by
    field_simp
    ring
  linarith

/-- **二维 Cauchy–Schwarz**：`(ac+bd)² ≤ (a²+b²)(c²+d²)`。
差的非负性就是 Lagrange 恒等式 `(a²+b²)(c²+d²) − (ac+bd)² = (ad−bc)²`，
`nlinarith` 自己找到它。 -/
theorem cauchy_schwarz_two (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]

/-- 30 个情形可以在核内直接判定：`ZMod 30` 上 `m⁵ = m`。
这是上面那条定理的全部计算量所在。 -/
example : ∀ m : ZMod 30, m ^ 5 = m := by decide

/-- `n⁵ ≡ n [MOD 30]`（等价于 `30 ∣ n⁵ − n`）。
先在有限环 `ZMod 30` 上判定，再用 `ZMod.natCast_eq_natCast_iff` 把等式翻译回
`Nat.ModEq`；全程只有核内 `decide`，没有 `native_decide`。 -/
theorem pow_five_mod_thirty (n : ℕ) : n ^ 5 ≡ n [MOD 30] := by
  have h : ∀ m : ZMod 30, m ^ 5 = m := by decide
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow]
  exact h _

/-- **立方和恒等式**，写成避免整除的形式：`4 · Σ_{i=0}^{n} i³ = (n(n+1))²`。 -/
theorem sum_cubes (n : ℕ) :
    4 * ∑ i ∈ Finset.range (n + 1), ((i : ℚ) ^ 3) = ((n : ℚ) * (n + 1)) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- 由加权 AM–GM 得到的经典推论：`abc = 1` 且 `a,b,c > 0` 时 `a + b + c ≥ 3`。 -/
theorem amgm_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1) :
    a + b + c ≥ 3 := by
  have key := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num) ha.le hb.le hc.le (by norm_num)
  have hr : (a * b * c) ^ (1 / 3 : ℝ) = a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := by
    rw [Real.mul_rpow (mul_nonneg ha.le hb.le) hc.le, Real.mul_rpow ha.le hb.le]
  have hone : (1 : ℝ) ^ (1 / 3 : ℝ) = 1 := by norm_num
  have hlow : (1 : ℝ) ≤ a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := by
    rw [← hr, h, hone]
  have hsum : a + b + c = 3 * ((1 / 3) * a + (1 / 3) * b + (1 / 3) * c) := by ring
  linarith

end Olympiad

end LeanProofs

#print axioms LeanProofs.Olympiad.hm_am3
#print axioms LeanProofs.Olympiad.nesbitt
#print axioms LeanProofs.Olympiad.cauchy_schwarz_two
#print axioms LeanProofs.Olympiad.pow_five_mod_thirty
#print axioms LeanProofs.Olympiad.sum_cubes
#print axioms LeanProofs.Olympiad.amgm_one
