# 验证说明

本工程给出了 Erdős Problem 279 肯定命题的无条件 Lean 4 证明。

最终定理为：

```lean
Erdos279.globalAffirmative : Erdos279.GlobalAffirmative
```

展开后，其命题是：

```lean
∀ k : Nat, 3 ≤ k → ∃ r : ResidueAssignment, CoversTail k r
```

也就是说：对每个 `k ≥ 3`，可以为每个素数选择一个非零约束下所需的
规范剩余类，使所有充分大的整数都获得商至少为 `k` 的覆盖。

## 已执行的检查

- Lean 工具链：`v4.27.0-rc1`
- 完整构建：`lake build`
- 公理审计：`lake env lean Erdos279/Audit.lean`
- 源码扫描：无 `sorry`、`admit`、`sorryAx`、自定义 `axiom`、
  `opaque` 或 `unsafe`

`#print axioms Erdos279.globalAffirmative` 的输出只有：

```text
[propext, Classical.choice, Quot.sound]
```

它们是 Lean 的标准逻辑基础，并非本工程额外加入的数学假设。

## 一键复核

在工程目录运行：

```powershell
./verify.ps1
```

脚本会依次执行全工程构建、公理审计和占位符扫描；任一步失败都会返回
非零退出码。

## 解析数论部分

工程已经在 Lean 中接通：

1. 固定等差数列素数定理；
2. 控制素数倒数和发散与密度网格；
3. 平移区间上的 Selberg 上界筛；
4. hard layer 的双剩余商筛；
5. 取 `⌊X^(1/64)⌋` 时的一致误差估计；
6. 所有 hard layers 的求和与容量严格不等式；
7. 动态调度、稳定化和最终全局赋值。

最后的 hard-layer 估计采用直接双剩余 Selberg 筛，因此不需要把
Bombieri–Vinogradov 或 Selberg–Delange 另列为未证明前提。
