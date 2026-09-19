# Lean 4 证明样例

Toolchain `leanprover/lean4:v4.31.0`，Mathlib pinned at `fabf563a7c9` (tag `v4.31.0`)。
CI: [`.github/workflows/ci.yml`](.github/workflows/ci.yml) 做 `lake build` 并审计 `sorry`。

这个仓库只有两个目的：证明我能写**编译通过、不依赖 `sorry`、不依赖现成结论**的 Lean 证明。
所有结论都用 `#print axioms` 审计过，只依赖 `propext, Classical.choice, Quot.sound`。

## 内容

| 文件 | 定理 | 陈述 | 规模 |
|---|---|---|---|
| [`LeanProofs/GammaVeblen.lean`](LeanProofs/GammaVeblen.lean) | `Ordinal.veblen_lt_gamma_zero` | `a < Γ₀ → b < Γ₀ → veblen a b < Γ₀` | 152 行，两条独立证明路线 |
| 同上 | `Ordinal.veblen_lt_of_fixed` | `veblen γ 0 = γ → a < γ → b < γ → veblen a b < γ`（抽象版，任意不动点） | 5 行 |
| 同上 | `Ordinal.veblen_lt_gamma` | 每个 `Γ_ o` 都对二元 Veblen 封闭 | 3 行 |
| [`LeanProofs/SchroederBernstein.lean`](LeanProofs/SchroederBernstein.lean) | `LeanProofs.csb` | `Injective f → Injective g → α ≃ β` | 121 行，从零 |

## Γ₀ 的封闭性

证明的核心不是迭代高度，而是不动点加字典序比较。`veblen_lt_veblen_iff` 把
`veblen o₁ a < veblen o₂ b` 完全拆成字典序的三种情形；取 `o₂ := γ` 并用
`veblen γ 0 = γ`，中间分支正好被 `a < γ` 与 `b < γ = veblen γ 0` 命中，于是
`veblen a b < γ`。`Γ₀`（以及每个 `Γ_ o`，见 `veblen_gamma_zero`）是该映射的不动点，
特例化即得。

第二条路线走 `lt_gamma_zero` 的有限迭代刻画：把 `a, b` 压进同一个
`(fun x => veblen x 0)^[n] 0`，则 `veblen a b` 被**下一个**迭代值压住
（`veblen_le_iterate_succ_veblen_zero`）。这条不比重构证明短，但它是独立的交叉验证。

配了三个非空转检查：`ω < Γ₀`、`φ ω ω < Γ₀`、`φ ε₀ ε₀ < Γ₀`，确认前提不是永假条件。

**关于新颖性的准确说法**：这条定理对 **mathlib 是新的**——全库 grep 后 `veblen` 只出现在
`Mathlib/SetTheory/Ordinal/Veblen.lean` 一个文件，该文件关于 `Γ₀` 只有
`veblen_gamma_zero`、`gamma_zero_eq_nfp`、`gamma_zero_le_of_veblen_le`、`lt_gamma_zero`、
`iterate_veblen_lt_gamma_zero`，没有任何封闭性陈述（文件头 TODO 只写着"证 `Γ₀` 可数"）。
但它在证明论教科书里是标准事实，**不是新数学**。适合当作 mathlib 的贡献提交，不适合当作研究结果宣传。

## Schröder–Bernstein

唯一的外部输入是 Knaster–Tarski（`OrderHom.lfp`，`Mathlib/Order/FixedPoints.lean`），
作用在 `Set α` 的单调自映射 `F s = (g '' (f '' s)ᶜ)ᶜ` 上。取不动点 `A := F.lfp`，
展开 `F A = A` 得到 CSB 的全部内容：

```
Aᶜ = g '' (f '' A)ᶜ
```

即 `f` 给出双射 `A ≃ f '' A`，`g` 给出双射 `(f '' A)ᶜ ≃ Aᶜ`，用
`Equiv.Set.sumCompl` + `Equiv.sumCongr` 拼成 `α ≃ β`。

**独立性自检**（这是这个文件真正想展示的部分）：把开头的 `import Mathlib` 换成

```
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Image
import Mathlib.Logic.Equiv.Set
```

文件照原样编译通过，而在这个收窄的前缀下 `schroeder_bernstein`、
`MeasurableEmbedding.schroederBernstein` 乃至 `Cardinal.mk` 全部是 unknown identifier。
也就是说，这个证明在类型层就够不到 mathlib 的现成 CSB 或任何基数算术路线。

## 本地验证

```bash
lake update
lake exe cache get        # 拉预编译 olean；失败则 lake build 从源码编译
lake build
```

逐个定理审计公理：

```bash
cat > Axioms.lean <<'EOF'
import LeanProofs
#print axioms Ordinal.veblen_lt_gamma_zero
#print axioms LeanProofs.csb
EOF
lake env lean Axioms.lean
```

本地实测输出（Lean 4.31.0 + 上述 mathlib rev，`lake env lean` 退出码 0，零 error 零 warning）：

```
'Ordinal.veblen_lt_gamma_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanProofs.csb' depends on axioms: [propext, Classical.choice, Quot.sound]
```

没有 `sorryAx`。

## 还没有的

`LeanProofs/Olympiad.lean`（竞赛题形式化）在写，写完会追加提交。
`Γ₀` 的可数性、`Γ₀` 作为 ATR₀ 证明论序数的那一整套（有序记号系统、单调可证偏序）
都不在这里，mathlib 目前也没有。
