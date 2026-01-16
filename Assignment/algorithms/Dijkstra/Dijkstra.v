Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.

Section Dijkstra.

(** Dijkstra算法用于计算单源最短路径。
    核心思想是贪心地选择当前距离最小的未访问顶点，然后松弛其邻居。
    
    算法流程：
    1. 初始化：源点距离为0，其他顶点距离为无穷大（W_inf）
    2. 循环：选择距离最小的未访问顶点u，标记为已访问
    3. 对u的每个邻居v，尝试通过u松弛：dist[v] = min(dist[v], dist[u] + weight(u,v))
    4. 重复直到所有可达顶点都被访问
    
    循环不变量核心思想：
    - 已访问顶点的dist值是最终的最短距离
    - 未访问顶点的dist值是"只能通过已访问顶点作为中间节点"的最短距离
    - 每次选择的顶点u，其dist[u]已经是真正的最短距离（贪心选择的正确性）
*)

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {step_valid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        (g: G)
        {g_valid: gvalid g}
        {eq_dec: EqDec V eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

(** 状态记录：已访问顶点集合 + 距离数组 *)
Record St: Type := mkSt {
  visited: V -> Prop;  (** 已访问的顶点集合 *)
  dist: V -> option Z;        (** 当前记录的距离，W_inf表示不可达 *)
}.

Context (src: V)  (** 源点 *)
        (valid_src: vvalid g src).

Instance: Settable St := settable! mkSt <visited; dist>.

(** 初始状态：源点距离为 g_zero，其他顶点距离为 W_inf *)
Definition initSt: St := {|
  visited := ∅;
  dist := fun v => if eq_dec v src then Some 0 else None;
|}.

(** 将顶点u标记为已访问 *)
Definition visit (u: V): program St unit :=
  update' (fun s => s <| visited ::= fun vs => vs ∪ [u] |>).

(** 松弛操作：对于边 e: u -> v，尝试更新 dist[v] = min(dist[v], dist[u] + weight(e)) *)
Definition relax_edge (u: V) (e: E): program St unit :=
  assume (fun s => exists v, step_aux g e u v);;
  v <- get (fun s v => step_aux g e u v);;
  update' (fun s => s <| dist ::= fun dist0 =>
    v !-> (le_min Z_op_le (dist0 v) (Z_op_plus (dist0 u) (weight g e))); dist0 |>).

(** 处理顶点u：标记为已访问，然后松弛所有出边 *)
Definition process_vertex (u: V): program St unit :=
  visit u;;
  forset (fun e => exists v, step_aux g e u v) 
    (relax_edge u).

(** 未访问且距离有限的顶点 *)
Definition unvisited (s: St) (u: V): Prop :=
  vvalid g u /\ ~ u ∈ s.(visited).

(** 选择距离最小的未访问可达顶点 *)
Definition select_min_vertex: program St V :=
  get (fun s u => min_object_of_subset Z_op_le (fun v => unvisited s v) (s.(dist)) u).

Definition unvisited_no_reachable (s : St): Prop :=
  forall v, unvisited s v -> ~reachable src v.

(** Dijkstra主算法：重复选择和处理顶点，直到没有未访问的可达顶点 *)
Definition Dijkstra: program St unit :=
  repeat_break (fun _ =>
    choice
      (assume (fun s => ~unvisited_no_reachable s);;
        u <- select_min_vertex;; 
        process_vertex u;;
        ret (by_continue tt))
      (assume (fun s => unvisited_no_reachable s);;
        ret (by_break tt))
  ) tt.


(** ===== 循环不变量定义 ===== 
    
    Dijkstra 算法的循环不变量刻画了算法执行过程中状态的关键性质。
    核心思想：将顶点分为已访问和未访问两类，分别维护不同的性质。
*)

(** 
  不变量 1: 已访问顶点的距离是最终的最短距离
  
  含义：对于任何已访问的顶点 v，dist[v] 已经是从源点到 v 的真正最短距离。
  
  形式化：v ∈ visited -> dist[v] = min_weight_distance(src, v)
  
  这是 Dijkstra 算法核心性质：一旦顶点被访问（确定），其距离就不会再改变。
*)

Definition visited_dist_final (s: St): Prop :=
  forall v, v ∈ s.(visited) -> 
    min_weight_distance g src v (s.(dist) v).

(** 
  不变量 2: 未访问顶点的距离是"仅通过已访问顶点"的最短距离
  
  含义：对于未访问的顶点 v，dist[v] 是所有"中间节点都在 visited 中"的路径的最短权重。
  
  形式化：v ∉ visited -> dist[v] = min_weight_distance_in_vset(src, v, visited)
  
  注意：
  - 如果 dist[v] = W_inf，表示通过 visited 无法到达 v
  - 一旦有新顶点 u 加入 visited，通过 u 可能发现更短的路径到达其他未访问顶点
*)
Definition unvisited_dist_optimal (s: St): Prop :=
  forall v, ~ v ∈ s.(visited) ->
    min_weight_distance_in_vset g src v (s.(visited)) (s.(dist) v).

(** 
  不变量 3: 源点性质
  
  含义：源点的距离始终为 g_zero（零元素）
  
  这是初始条件，也是算法的基础。
*)
Definition source_dist_zero (s: St): Prop :=
  s.(dist) src = Some 0.

(** 
  不变量 4: 有效性约束
  
  含义：只有图中的有效顶点才会被访问，且只有有效顶点的距离才可能不是 W_inf
  
  这是健全性的基础。
*)
Definition validity_constraint (s: St): Prop :=
  forall v, v ∈ s.(visited) -> vvalid g v.

(** 完整的循环不变量 *)
Definition loop_invariant (s: St): Prop :=
  visited_dist_final s /\
  unvisited_dist_optimal s /\
  source_dist_zero s /\
  validity_constraint s.


(** ===== 贪心选择的正确性 ===== 
    
    Dijkstra 算法的关键是贪心选择：每次选择 dist 值最小的未访问顶点 u，
    可以保证 dist[u] 已经是真正的最短距离。
    
    为什么？（反证法）
    假设存在更短的路径 P: src ~> u，其权重 < dist[u]。
    考虑 P 上第一个离开 visited 集合的顶点 v：
    - v 的前驱在 visited 中，所以 dist[v] ≤ weight(P 的前缀到 v)
    - 因为权重非负，weight(P 的前缀到 v) < weight(P) < dist[u]
    - 所以 dist[v] < dist[u]
    - 但我们选择了 u 而不是 v，矛盾！（u 应该是最小的）
    
    这个性质保证了贪心策略的正确性。
*)
(**
  贪心选择引理（Dijkstra 算法的核心）
  
  假设：
  - 所有已访问顶点的 dist 值都是最终的最短距离
  - 所有未访问顶点的 dist 值是仅通过已访问顶点的最短距离
  - 选择 dist 值最小的未访问顶点 u
  
  则：dist[u] 已经是从 src 到 u 的真正最短距离
  
  证明（反证法）：
  假设存在更短的路径 P: src ~> u，权重 < dist[u]。
  
  考虑 P 上第一个离开 visited 集合的顶点 v：
  - v 的前驱 w 在 visited 中
  - 根据循环不变量，dist[w] = 真正的最短距离到 w
  - 经过 w 到达 v 的路径权重 ≥ dist[w] + weight(w, v)
  - 根据循环不变量，dist[v] ≤ dist[w] + weight(w, v)
    （因为 dist[v] 是通过 visited 的最短距离，包括经过 w 的路径）
  
  所以：dist[v] ≤ weight(P 的前缀到 v) < weight(P) < dist[u]
  
  但这与"选择了 u"矛盾，因为我们应该选择 dist 值最小的顶点 v。
  
  关键：这个证明依赖于边权重非负！
*)

Lemma Assertion (p_any : P) (vis_set : V -> Prop): 
  ~(tail p_any) ∈ vis_set ->
  exists v p_pre,
    In v (vertex_in_path p_any) /\
    is_path_through_vset g p_pre src v vis_set /\
    ~ v ∈ vis_set /\
    Z_op_le (path_weight g p_pre) (path_weight g p_any).
Proof.
  intros.
Admitted.

Lemma greedy_choice_lemma:
  forall (src u: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 前提：循环不变量成立 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* u 是未访问顶点中 dist 值最小的 *)
    ~ u ∈ visited ->
    dist u <> None ->
    (forall v, ~ v ∈ visited -> dist v <> None -> Z_op_le (dist u) (dist v)) ->
    (* 结论：dist[u] 是最终的最短距离 *)
    min_weight_distance g src u (dist u).
Proof.
  intros src_g u_target vis_set d_map H_vis_ok H_unvis_ok H_u_not_vis H_u_some H_u_is_min.

  (* 利用未访问点的不变量 (H_unvis_ok) 分析 u 的状态 *)
  pose proof (H_unvis_ok u_target H_u_not_vis) as H_u_status.
  destruct H_u_status as [H_path_exists | H_path_none].

  (* 情况 A: 局部路径存在 (dist u = Some) *)
  - destruct H_path_exists as [H_struct_u H_val_u].
    destruct H_struct_u as [p_best [H_p_thru_vis H_p_weight_is_dist]].
    
    (* [STEP 1] 选择 "存在最短路" 的分支 *)
    left. 
    
    (* [STEP 2] 这是一个存在量词，必须先提供 witness (p_best) *)
    exists p_best. 
    
    (* [STEP 3] 现在的目标是 (是最小路径) /\ (权重相等) *)
    split.
    
    { (* 子目标 1: 证明 p_best 是最小路径 (min_object) *)
      split.
      - (* 1.1 证明它是一条合法路径 *)
        destruct H_p_thru_vis as [H_is_path _].
        exact H_is_path.
        
      - (* 1.2 证明它是所有路径中最短的 (核心难点) *)
        intros p_any H_p_any_valid.
        
        (* === 使用 Assertion (Cut Property) === *)
        (* 首先明确 p_any 的终点是 u_target *)
        assert (H_tail: tail p_any = u_target).
        { destruct H_p_any_valid as [_ [_ H_t]]. exact H_t. }
        
        (* 因为终点 u 未被访问，路径上必然存在分割点 *)
        rewrite <- H_tail in H_u_not_vis.
        pose proof (Assertion p_any vis_set H_u_not_vis) as H_cut.
        destruct H_cut as [v [p_pre [H_v_in [H_pre_thru_vis [H_v_not_vis H_weight_mono]]]]].
        
        (* === 构建不等式链: dist u <= dist v <= weight p_pre <= weight p_any === *)
        
        (* 分析分割点 v 的性质 *)
        pose proof (H_unvis_ok v H_v_not_vis) as H_v_opt.
        
        (* 必须证明 dist v 是 Some (不是无穷大)，否则无法比较 *)
        destruct (d_map v) eqn:H_dist_v.
        + (* Case: dist v = Some z *)
          (* 1. 使用贪心选择性质: dist u <= dist v *)
          assert (H_greedy: Z_op_le (d_map u_target) (d_map v)).
          { apply H_u_is_min; [exact H_v_not_vis | rewrite H_dist_v; congruence]. }
          
          (* 2. 使用 v 的局部最优性: dist v <= weight p_pre *)
          assert (H_v_local: Z_op_le (d_map v) (path_weight g p_pre)).
          {
            destruct H_v_opt as [[_ H_min] | H_impossible].
            - apply H_min. exact H_pre_thru_vis.
            - (* 矛盾: 不变量说不可达，但 p_pre 确实存在 *)
              exfalso. apply H_impossible. exists p_pre. exact H_pre_thru_vis.
          }
          
          (* 3. 串联所有不等式 *)
          rewrite H_p_weight_is_dist. (* dist u = weight p_best *)
          eapply Z_op_le_trans with (y := d_map v).
          * exact H_greedy.
          * eapply Z_op_le_trans with (y := path_weight g p_pre).
            -- exact H_v_local.
            -- exact H_weight_mono.
            
        + (* Case: dist v = None (矛盾情况) *)
          exfalso.
          destruct H_v_opt as [[_ H_eq] | H_none].
          * (* 如果不变量说有值，但现在是 None *)
            rewrite H_dist_v in H_eq. discriminate.
          * (* 如果不变量说不可达，但 p_pre 存在 *)
            apply H_none. exists p_pre. exact H_pre_thru_vis.
    }
    
    { (* 子目标 2: 证明权重相等 *)
      exact H_p_weight_is_dist.
    }

  (* 情况 B: 局部路径不存在 (dist u = None) *)
  - destruct H_path_none as [_ H_is_none].
    (* 前提 H_u_some 说 dist u <> None，产生直接矛盾 *)
    rewrite H_is_none in H_u_some.
    congruence.
Admitted.

Definition greedy_choice_correct (s: St) (u: V): Prop :=
  unvisited s u ->
  (forall v, unvisited s v -> Z_op_le (s.(dist) u) (s.(dist) v)) ->
  min_weight_distance g src u (s.(dist) u) \/ dist s u = None.

(* TODO *)
Lemma greedy_choice_correct_prop (s: St) (u: V):
  loop_invariant s ->
  greedy_choice_correct s u.
Proof.
  intros H_inv.
  unfold greedy_choice_correct.
  intros H_unvisited H_minimal.
  destruct H_inv as [H_vis_final [H_unvis_opt [H_src_valid H_validity]]].

  (* 分类讨论 dist s u 是 数 还是 None *)
  destruct (dist s u) eqn:H_dist_val.
  - (* dist s u 是数 *)
    rewrite <- H_dist_val.
    left.
    apply (greedy_choice_lemma src u (visited s) (dist s)).
      + apply H_vis_final.
      + apply H_unvis_opt.
      + destruct H_unvisited; assumption.
      + rewrite H_dist_val. congruence.
      + (* u 是距离 s 最小的*)
        rewrite H_dist_val.
        intros v H_v_not_vis H_v_dist_some.
        apply H_minimal.
        split.
        * admit. (* 证明 vvalid g v ？有些疑惑*)
        * exact H_v_not_vis.
  -
    unfold unvisited_dist_optimal in H_unvis_opt.
    right.
    reflexivity.
Admitted.

Definition select_min_vertex_prop_wrap (u : V) (s : St): Prop :=
  unvisited s u /\
    (forall v, unvisited s v -> Z_op_le (s.(dist) u) (s.(dist) v)).

(* TODO : 一个包装的性质函数 *)
Lemma select_min_vertex_prop: 
  Hoare
    (fun s1 => loop_invariant s1)
    select_min_vertex
    (fun u s2 => loop_invariant s2 /\ select_min_vertex_prop_wrap u s2). (* TODO: 包装性质 *)
Proof.
Admitted.

(* TODO *)
Lemma process_vertex_holds_inv (u : V):
  Hoare
    (fun s1 => loop_invariant s1 /\ select_min_vertex_prop_wrap u s1)
    (process_vertex u)
    (fun _ s2 => loop_invariant s2).
Proof.
Admitted.


(** ===== 正确性规范 ===== *)

(** 健全性：记录的距离是真实的最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall v w, s.(dist) v = w -> min_weight_distance g src v w.

(** 完备性：真实的最短距离被正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall v w, min_weight_distance g src v w -> s.(dist) v = w.

(** 完整正确性：健全性 + 完备性 *)
Definition distance_correct (s: St): Prop :=
  distance_soundness s /\ distance_completeness s.


(** ===== 主定理 ===== 
    
    定理：Dijkstra 算法在初始状态 initSt 上执行，最终得到正确的单源最短路径。
    
    证明路线：
    
    【第一步】证明初始状态满足循环不变量
      需要证明：loop_invariant initSt
      - visited_dist_final: 空集，条件为假，成立
      - unvisited_dist_optimal: 所有顶点都未访问，visited = ∅
        需要证明：对于每个顶点 v
        * 如果 v = src: dist[v] = g_zero，且这是通过空集的最短距离（空路径）
        * 如果 v ≠ src: dist[v] = W_inf，且通过空集无法到达
      - source_dist_zero: 根据 initSt 定义成立
      - validity_constraint: 空集，成立
    
    【第二步】证明循环体保持不变量
      假设 loop_invariant s 成立，选择顶点 u 并处理。
      
      步骤 2.1: 证明 greedy_choice_correct s u
        - 使用反证法
        - 关键：非负权重 + dist[u] 是未访问顶点中最小的
      
      步骤 2.2: 将 u 加入 visited 后
        新状态 s': visited' = visited ∪ {u}
        需要证明：
        a) visited_dist_final s' 成立
           - 对于 v ∈ visited: 沿用 s 的性质
           - 对于 v = u: 使用 greedy_choice_correct
        
        b) unvisited_dist_optimal s' 成立
           - 松弛操作前：dist[v] 是通过 visited 的最短距离
           - 松弛操作后：dist[v] = min(dist[v], dist[u] + weight(u, v))
           - 需要证明这是通过 visited ∪ {u} 的最短距离
           - 使用类似 Floyd 的 relaxation_correct 引理
    
    【第三步】证明终止性
      - 每次循环减少未访问顶点数量
      - 有限图保证算法终止
    
    【第四步】证明终止时的正确性
      终止条件：不存在 unvisited_reachable 的顶点
      即：所有可达顶点都已访问
      
      根据循环不变量：
      - 所有已访问顶点的距离正确（visited_dist_final）
      - 未访问顶点的距离为 W_inf（不可达）
      
      因此：distance_correct 成立
*)

Definition continue_bind_aux (a : CntOrBrk unit unit): St -> Prop :=
  match a with
  | by_continue _=> fun s => loop_invariant s
  | by_break _ => fun _ => True
  end.

(* ✅ *)
Lemma continue_holds_invariant:
  Hoare
  (fun s : St => loop_invariant s)
  (x <- choice
      (assume (fun s => ~unvisited_no_reachable s);;
        u <- select_min_vertex;; 
        process_vertex u;;
        ret (by_continue tt))
      (assume (fun s => unvisited_no_reachable s);;
        ret (by_break tt));;
    continue_case x)
  (fun (_ : unit) (s : St) => loop_invariant s).
Proof.
  apply Hoare_bind with (Q := continue_bind_aux).
  2:{ intros. 
      destruct a; unfold continue_case.
      - apply Hoare_ret'; intros.
        apply H.
      - apply Hoare_empty. }
  apply Hoare_choice.
  2:{ apply Hoare_assume_bind.
      apply Hoare_ret'.
      intros. simpl. tauto. }
  apply Hoare_assume_bind.
  apply Hoare_bind with (Q := fun u s => loop_invariant s /\ select_min_vertex_prop_wrap u s).
  1:{ apply Hoare_conseq_pre with (P2 := fun s => loop_invariant s).
      - intros. destruct H. auto.
      - apply select_min_vertex_prop. }
  intros u. (* process 取出的顶点 *)
  apply Hoare_bind with (Q := fun _ s => loop_invariant s).
  1:{ apply process_vertex_holds_inv. }
  intros _.
  apply Hoare_ret'.
  intros. simpl. auto.
Qed.

Definition break_bind_aux (a : CntOrBrk unit unit): St -> Prop :=
  match a with
  | by_continue _=> fun _ => True
  | by_break _ => fun s => distance_correct s
  end.

(* TODO *)
Lemma distance_correct_aux (s : St):
  unvisited_no_reachable s ->
  loop_invariant s ->
  distance_correct s.
Proof.
Admitted.

(* ✅ *)
Lemma termination_implies_correctness:
  Hoare
  (fun s : St => loop_invariant s)
  (x <- choice
      (assume (fun s => ~unvisited_no_reachable s);;
        u <- select_min_vertex;; 
        process_vertex u;;
        ret (by_continue tt))
      (assume (fun s => unvisited_no_reachable s);;
        ret (by_break tt));;
    break_case x)
  (fun (_ : unit) (s : St) => distance_correct s).
Proof.
  apply Hoare_bind with (Q := break_bind_aux).
  2:{ intros. 
      destruct a; unfold break_case.
      - apply Hoare_empty.
      - apply Hoare_ret'; intros.
        apply H. }
  hoare_auto. (* 怎么突然又有了🤔 *)
  1:{ apply Hoare_bind with (Q := fun u s => loop_invariant s /\ select_min_vertex_prop_wrap u s).
      1:{ apply Hoare_conseq_pre with (P2 := fun s => loop_invariant s).
      - intros. destruct H. auto.
      - apply select_min_vertex_prop. }
      intros u. (* process 取出的顶点 *)
      apply Hoare_bind with (Q := fun _ s => loop_invariant s).
      1:{ apply process_vertex_holds_inv. }
      intros _.
      apply Hoare_ret'.
      intros. simpl. auto. }
  simpl. destruct H.
  apply distance_correct_aux; auto.
Qed.

Lemma empty_path_is_nil : 
  edge_in_path (empty_path src) = nil.
Proof.
  unfold edge_in_path, empty_path.
  remember path as p0 eqn:Hp.
  destruct p0 as [pv vip hd hv tl tv eip ve].
  cbn.
  remember emptypath as ep0 eqn:Hep.
  destruct ep0 as [empty_path0 dummy Hnil]. 
  cbn.
  pose proof (dummy g src) as Hvalid.
  pose proof (ve g (empty_path0 src) Hvalid) as Hve.
  assert (Hvip : forall p0 : P, vip p0 = vertex_in_path (Path:=path) p0).
  {
    intro p0.
    rewrite <- Hp.
    cbn.
    reflexivity.
  }
  rewrite (Hvip (empty_path0 src)) in Hve.
  assert (Hnil' : forall v : V, vertex_in_path (Path:=path) (empty_path0 v) = v :: nil).
  {
    intro v.
    rewrite <- Hp.
    cbn.
    exact (Hnil v).
  }
  rewrite (Hnil' src) in Hve.
  destruct Hve as [Hlen _]. 
  simpl in Hlen.
  assert (H0 : length (eip (empty_path0 src)) = 0%nat) by lia.
  apply length_zero_iff_nil in H0.
  exact H0.
Qed.
  
(* TODO *)
Lemma min_weight_distance_in_vset_empty (v : V):
  min_weight_distance_in_vset g src v ∅ (dist initSt v) . (*不经过任何点的距离就是一开始的dist记录的距离；src-src -> 0=0; src-v -> None = None*)
Proof.
  unfold min_weight_distance_in_vset.
  unfold min_value_of_subset_with_default.
  destruct (eq_dec v src).
  - left. split.
    + (*空路径0 = initSt中空路径0*)
      admit.
    + (* Some 0 < None *)
      rewrite e.
      simpl.
      destruct (eq_dec src src) as [_ | contra]; simpl; tauto.
  - right. split.
    + intros.
      assert (path_weight g a = None).
      {
        destruct H as [Hpath H_through_empty].
        destruct Hpath as [Hvalid [Hhead Htail]].
        pose proof (destruct_1n_spec g a Hvalid) as Hspec.
        destruct (destruct_1n_path a) eqn:Ha_struct.
        * (* Case 1: a 是空路径 (Base Case) *)
          rewrite Hspec in Hhead, Htail. 
          pose proof (empty_path_vertex v0) as Hv.
          pose proof (head_valid g (empty_path v0) (empty_path_valid g v0)) as Hh.
          pose proof (tail_valid g (empty_path v0) (empty_path_valid g v0)) as Ht.
          rewrite Hv in Hh, Ht.
          simpl in Hh, Ht.
          injection Hh.  (* 得到 head (empty_path v0) = v0 *)
          injection Ht.  (* 得到 tail (empty_path v0) = v0 *)
          intros.
          rewrite Hhead in H0.
          rewrite Htail in H.
          subst v0. (* 把 v0 替换成 src *)
          subst v.  (* 把 v 替换成 src *)
          congruence.
        * (* Case 2: a 是非空 + 空路径p *)
          destruct Hspec as [Hp'valid [Hp'head [Hstep Ha_eq]]].
          subst a.
          admit.
      }
      rewrite H0; simpl; tauto.
    + simpl.
      destruct (eq_dec v src); [contradiction|].
      reflexivity.
Admitted.


(* TODO *)
Lemma init_satisfies_invariant:
  forall s : St, s = initSt -> loop_invariant s.
Proof.
  intros.
  unfold loop_invariant.
  split; [|split; [|split]]; rewrite H.
  - unfold visited_dist_final.
    intros. simpl in H0. tauto.
  - unfold unvisited_dist_optimal.
    intros.
    assert (visited initSt = ∅).
     {simpl. reflexivity. }
    rewrite H1.
    apply min_weight_distance_in_vset_empty.
  - unfold source_dist_zero; simpl.
    destruct (eq_dec src src); [reflexivity|].
    contradiction c; reflexivity. (* 没看懂但总是还是contradiction出来了 *)
  - unfold validity_constraint.
    intros. simpl in H0. tauto.
Qed.



(* ✅ *)
Theorem Dijkstra_correct:
  Hoare (fun s => s = initSt)
        Dijkstra
        (fun _ s => distance_correct s).
Proof.
  unfold Dijkstra.
  apply Hoare_conseq_pre with (P2:= fun s => loop_invariant s).
  1:{ apply init_satisfies_invariant. } (* init_satisfies_invariant: initSt 满足 loop_invariant *)
  apply Hoare_repeat_break' with (P:= fun _ s => loop_invariant s); intros.
  - apply continue_holds_invariant.
  - apply termination_implies_correctness.
Qed.
  (** 
    提示：
    1. 使用 Hoare_repeat_break 规则
    2. 以 loop_invariant 作为循环不变量
    3. 需要证明的关键引理：
       - init_satisfies_invariant: initSt 满足 loop_invariant
       - visit_preserves_invariant: 访问顶点保持不变量
       - relax_preserves_invariant: 松弛操作保持不变量
       - greedy_choice_lemma: 贪心选择的正确性
       - termination_implies_correctness: 终止时不变量蕴含正确性
  *)

End Dijkstra.