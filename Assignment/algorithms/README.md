# Algorithms - 图论算法证明指南

本目录包含四个经典图论算法的 Coq 形式化及证明骨架，文件中所有 `Admitted.` 处需要你补全证明。

## 目录结构
- `Dijkstra/`：单源最短路径，主定理 `Dijkstra_correct`，说明见 `Dijkstra.pdf`
- `Floyd/`：全源最短路径，主定理 `Floyd_correct`，说明见 `Floyd.pdf`
- `Prim/`：Prim 最小生成树，主定理 `Prim_correct`，说明见 `Prim.pdf`
- `Kruskal/`：Kruskal 最小生成树，主定理 `Kruskal_correct`，说明见 `Kruskal.pdf`
- `MapLib.v`：简单函数式映射工具，提供 `_ !-> v`、`x !-> v ; m` 等记号
- `Tactics.v`：自定义战术 `my_destruct`，用于递归拆解存在式/合取/析取
- `makefile`：算法子工程的编译脚本（自动生成 `_CoqProject`）

## 环境与依赖
- 建议版本：Coq 8.20.1（与根目录 README 保持一致）
- 在编译本目录前，先在仓库根目录按顺序编译依赖库：
  1) `sets` 2) `fixedpoints` 3) `coq-record-update` 4) `monadlib`
  5) `ListLib` 6) `MaxMinLib` 7) `graph_lib`

## 编译方法
```bash
cd algorithms
# 生成 _CoqProject
make _CoqProject

# 全量编译
make

# 只编译单个算法
make Dijkstra/Dijkstra.vo
make Floyd/Floyd.vo
make Prim/Prim.vo
make Kruskal/Kruskal.vo

# 生成依赖文件（可选）
make depend

# 清理生成文件
make clean
```
- 如需指定 Coq 安装路径，可在命令前设置 `COQBIN=path/to/coq/bin/`。

## 关键文件提示
- `MapLib.v`：基于 `EqDec` 的全函数映射，常用记号：
  - `_ !-> v` 构造常量映射；`x !-> v ; m` 在 `m` 上更新键 `x`
- `Tactics.v`：`my_destruct H` 可递归拆解 `exists`/`/\`/`\/`，遇到矛盾会尝试 `discriminate` 或 `contradiction`
- `Dijkstra.v`：已给出状态定义、选择最小未访问顶点、循环不变量草稿及证明路线提示
- `Floyd.v`：已给出 `Floyd_loop_invariant` 与 `distance_correct` 规范，主循环使用 `forset`
- `Prim.v`：状态含 `in_tree` 与 `mst_edges`，切边选择基于 `min_object_of_subset`，需要完成 `Prim_correct`
- `Kruskal.v`：状态为边集，`selectable_edge` 需保证不成环，目标 `Kruskal_correct`

## 证明建议
- 循环算法：先确立循环不变量，引入必要的辅助引理（如松弛保持性、终止性度量）。
- 路径相关结论：善用 `GraphLib` 中的可达性与路径分解引理；对权重最小性使用 `MaxMinLib`。
- 状态更新：`RecordUpdate` 的 `<| field ::= ... |>` 记号可与 `update'` 配合，减少手动拆解记录。
- 处理存在式/拆分条件时，可先 `intros` 后使用 `my_destruct` 简化上下文。

## 提交要求回顾
- 所有 `Admitted.` 替换为完整证明，`make` 能无误通过。
- 若修改接口或新增引理，保持记号与命名的一致性，避免破坏已有脚本。

