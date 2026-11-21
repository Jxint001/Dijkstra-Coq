Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets_scope.
Local Open Scope monad_scope.
Local Open Scope map_scope.
Local Open Scope Z_scope.

Section Dijkstra.

(** Dijkstra算法用于计算单源最短路径。
    核心思想是贪心地选择当前距离最小的未访问顶点，然后松弛其邻居。
    
    算法流程：
    1. 初始化：标记源点，源点距离为 0，直接后继取边权，其余顶点取 None
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

Context (src: V)  (** 源点 *)
        (valid_src: vvalid g src).

(*简单图 不存在u-v的多条（边权不等的）重边*)
Context {simple_graph: forall u v e1 e2, step_aux g e1 u v -> step_aux g e2 u v -> e1 = e2}.
(* Dijkstra要求边权非负 *)
Context {weight_nonneg: forall e w, weight g e = Some w -> 0 <= w}.
(* 边的边权不是None/无穷大 *)
Context (weight_defined: forall u v e, step_aux g e u v -> weight g e <> None).

(** 状态记录：已访问顶点集合 + 距离数组 *)
Record St: Type := mkSt {
  visited: V -> Prop;  (** 已访问的顶点集合 *)
  dist: V -> option Z;        (** 当前记录的距离，W_inf表示不可达 *)
}.

Instance: Settable St := settable! mkSt <visited; dist>.

(** 初始状态已处理源点的所有出边 *)

Definition initSt: St := {|
  visited := [src];
  dist := fun v => 
    if eq_dec v src then Some 0
    else 
      epsilon (inhabits None) 
        (fun (ow : option Z) => 
          (exists (e : E), step_aux g e src v /\ weight g e = ow) \/
          (ow = None /\ ~exists (e : E), step_aux g e src v))
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

Lemma epath_weight_nonneg: forall p, Z_op_lt (epath_weight g p) (Some 0) -> False.
Proof.
  intros p Hlt.
  revert Hlt.
  induction p as [|e p IH]; intro Hlt.
  - (* p = nil *)
    unfold Z_op_lt in Hlt.
    destruct Hlt as [_ Hneq].
    unfold epath_weight in Hneq; simpl in Hneq.
    apply Hneq; reflexivity.
  - (* p = e :: p *)
  unfold Z_op_lt in Hlt.
  destruct Hlt as [Hle Hneq].
  unfold epath_weight in Hle, Hneq; simpl in Hle, Hneq.
  change (fold_right Z_op_plus (Some 0) (map (weight g) p))
    with (epath_weight g p) in Hle, Hneq.
  destruct (weight g e) as [we|] eqn:Hwe.
  + pose proof (weight_nonneg e we Hwe) as Hwe_ge0.
    destruct (epath_weight g p) as [wp|] eqn:Hwp.
    * simpl in Hle, Hneq.
      assert (wp <= 0) by lia.
      assert (0 <= wp).
      { (* 反证 *)
        destruct (Z_le_gt_dec 0 wp) as [H0|Hneg]; auto.
        exfalso.
        apply (IH).
        unfold Z_op_lt.
        split.
        - simpl. lia.
        - intro Heq. inversion Heq. lia.
      }
      assert (wp = 0) by lia. subst wp.
      simpl in Hle, Hneq.
      assert (we = 0) by lia. subst we.
      apply Hneq. reflexivity.
    * simpl in Hle. contradiction.
  + simpl in Hle. contradiction.
Qed.


(** ===== 循环不变量定义 ===== 
    
    Dijkstra 算法的循环不变量刻画了算法执行过程中状态的关键性质。
    核心思想：将顶点分为已访问和未访问两类，分别维护不同的性质。
*)

(** 
  不变量 1: 已访问顶点的距离是最终的最短距离
  
  含义：对于任何已访问的顶点 v，dist[v] 已经是从源点到 v 的真正最短距离。
  
  形式化：v ∈ visited -> dist[v] = min_value_weight_epath(src, v)
  
  这是 Dijkstra 算法核心性质：一旦顶点被访问（确定），其距离就不会再改变。
*)

Definition visited_dist_final (s: St): Prop :=
  forall v, v ∈ s.(visited) -> 
    min_value_weight_epath g src v (s.(dist) v).

(** 
  不变量 2: 未访问顶点的距离是"仅通过已访问顶点"的最短距离
  
  含义：对于未访问的顶点 v，dist[v] 是所有"中间节点都在 visited 中"的路径的最短权重。
  
  形式化：v ∉ visited -> dist[v] = min_value_weight_epath_in_vset(src, v, visited)
  
  注意：
  - 如果 dist[v] = W_inf，表示通过 visited 无法到达 v
  - 一旦有新顶点 u 加入 visited，通过 u 可能发现更短的路径到达其他未访问顶点
*)
Definition unvisited_dist_optimal (s: St): Prop :=
  forall v, ~ v ∈ s.(visited) ->
    min_value_weight_epath_in_vset g src v (s.(visited)) (s.(dist) v).

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

(** 
  不变量 5: 关于可达性
    (1) visited s v -> reachable v
    (2) no_reachable将始终保持为None *)
Definition reachable_prop (s : St): Prop :=
  (forall v, visited s v -> reachable src v) /\ 
  (forall v, ~reachable src v -> dist s v = None). 

(** 完整的循环不变量 *)
Definition loop_invariant (s: St): Prop :=
  visited_dist_final s /\
  unvisited_dist_optimal s /\
  source_dist_zero s /\
  validity_constraint s /\
  reachable_prop s.

(* 合法路径的长度不为 None *)
Lemma valid_epath_not_none:
  forall u p v, valid_epath g u p v -> epath_weight g p <> None.
Proof.
  intros u p v Hval.
  revert u v Hval.
  induction p as [|e p' IH]; intros u v Hval.
  - (* p = nil *)
    discriminate.
  - (* p = e :: p' *)
    apply valid_epath_cons_inv in Hval.
    destruct Hval as [v_next [Hstep Hrest]].
    unfold epath_weight. simpl.
    (* 利用 weight_defined 证明头边 e 的权重不是 None *)
    pose proof (weight_defined _ _ _ Hstep) as Hwe_def.
    destruct (weight g e) as [we|] eqn:Hwe.
    + (* 头边权重存在 (Some we) *)
      (* 利用归纳假设证明剩余路径 p' 的权重不是 None *)
      specialize (IH v_next v Hrest).
      unfold epath_weight in IH.
      destruct (fold_right Z_op_plus (Some 0) (map (weight g) p')) as [w_rest|] eqn:Hwp.
      * unfold Z_op_plus. discriminate.
      * contradiction.
    + contradiction.
Qed.

(* 合法路径的长度非负 *)
Lemma valid_epath_non_neg:
  forall u p v w, valid_epath g u p v -> epath_weight g p = Some w -> 0 <= w.
Proof.
  intros u p v w Hval Hw.
  revert u v w Hval Hw.
  (* 对路径 p 进行归纳 *)
  induction p as [|e p' IH]; intros.
  - (* p = nil *)
    simpl in Hw.
    injection Hw as Heq; subst.
    lia.  
  - (* p = e :: p' *)
    simpl in Hw.
    (* unfold Z_op_plus in Hw. *)
    destruct (weight g e) as [we|] eqn:Heq_e. 
    2:{
        unfold epath_weight in Hw. 
        unfold map, fold_right in Hw.
        rewrite Heq_e in Hw. discriminate. }
    unfold epath_weight in Hw. simpl in Hw.
    rewrite Heq_e in Hw.
    pose proof (weight_nonneg _ _ Heq_e) as Hwe_ge0.
    change (fold_right Z_op_plus (Some 0) (map (weight g) p')) 
      with (epath_weight g p') in Hw.
    destruct (epath_weight g p') as [wp|] eqn:Hwp.
    2:{ simpl in Hw. discriminate. }
    simpl in Hw. injection Hw as Heq_w. subst w.
    apply valid_epath_cons_inv in Hval.
    destruct Hval as [v_next [_ Hval_rest]].
    rewrite <- Hwp in IH.
    specialize (IH v_next v wp Hval_rest Hwp).
    lia.
Qed.

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

Lemma greedy_cut (p_any : list E) (v_end : V) (vis_set : V -> Prop): 
  valid_epath g src p_any v_end -> (* 通过这种方式来确定终点 *)
  ~ v_end ∈ vis_set ->
  exists v p_pre,
    v ∈ (epath_to_vset g src p_any) /\
    is_epath_through_vset g src p_pre v vis_set /\
    ~ v ∈ vis_set /\
    Z_op_le (epath_weight g p_pre) (epath_weight g p_any).
Proof.
  intros H_path_any H_end_not_vis.
  generalize dependent src.
  induction p_any as [|e p IH]; intros u H_u_valid H_path.
  - (* p nil *)
    apply valid_epath_nil_inv in H_path. subst.
    exists v_end, nil.
    repeat split.
    + exists nil, nil. split; [reflexivity|].
      apply valid_epath_empty.
    + apply is_epath_through_vset_nil. auto.
    + intros p1 p2 x Hp1 Hp2 Heq.
      symmetry in Heq.
      apply app_eq_nil in Heq.
      destruct Heq as [Hnil1 Hnil2].
      subst.
      contradiction.
    + exact H_end_not_vis.
    + simpl. lia.
  - (* e::p *)
    apply valid_epath_cons_inv in H_path.
    destruct H_path as [w [H_step H_path_w]].
    destruct (classic (u ∈ vis_set)) as [H_u_vis | H_u_not_vis].
    + (* u ∈ vis_set (必须向后继续寻找) *)
      destruct (classic (w ∈ vis_set)) as [H_w_vis | H_w_not_vis].
      * (* 下一步 w 也在 vis_set 中 -> 递归 *)
        assert (H_w_valid: vvalid g w).
        {
          destruct step_valid as [_ step_valid_dst_lemma]. 
          eapply step_valid_dst_lemma.
          apply H_step.
        }
        specialize (IH w H_w_valid H_path_w).
        destruct IH as [v [p_pre_rest [H_v_in [H_thru [H_v_not_vis H_weight]]]]].
        exists v, (e :: p_pre_rest).
        repeat split.
        -- destruct H_v_in as [p1 [p2 [Hp1_eq Hp1_val]]].
           exists (e :: p1), p2. 
           split; [simpl; rewrite Hp1_eq; reflexivity |].
           eapply valid_epath_cons; eauto.
        -- unfold is_epath_through_vset in *.
           destruct H_thru as [H_valid_rest H_iff_rest].
           eapply valid_epath_cons.
           { exact H_step. }
           { exact H_valid_rest. }
        -- intros p1 p2 x Hp1 Hp2 Heq Hval.
           destruct p1 as [| e_head p1_tail].
           { contradiction. }
           simpl in Heq. injection Heq as He_eq Hrest. subst e_head.
           destruct p1_tail as [| e_next p1_rest].
           (* 对 p1 的尾部进行讨论 *)
           ** (* p1 = [e]，切分点 x 即为 w *)
            apply valid_epath_single_inv in Hval.
            assert (x = w).
            { symmetry; eapply step_aux_unique; eauto. }
            subst x.
            apply H_w_vis.
           ** (* p1 = e :: e_next :: p1_rest，切分点在 p_pre_rest 内部 *)
            apply valid_epath_cons_inv in Hval.
            destruct Hval as [w' [Hstep' Hval_rest]].
            assert (w' = w).
            { eapply step_aux_unique; eauto. }
            subst w'. 
            unfold is_epath_through_vset in H_thru.
            destruct H_thru as [H_valid_whole H_iff_thru].
            apply H_iff_thru with (p1 := e_next :: p1_rest) (p2 := p2).
              ++ discriminate.
              ++ apply Hp2.
              ++ apply Hrest.
              ++ apply Hval_rest.
        -- exact H_v_not_vis.
        -- unfold epath_weight; simpl.
           change (fold_right Z_op_plus (Some 0) (map (weight g) p_pre_rest)) with (epath_weight g p_pre_rest).
           change (fold_right Z_op_plus (Some 0) (map (weight g) p)) with (epath_weight g p).
           destruct (weight g e) as [we | ].
           **(* 对两个路径的权重进行分类讨论 *)
             destruct (epath_weight g p_pre_rest) as [w_pre | ].
             ++ destruct (epath_weight g p) as [w_p | ].
              *** (* p 也有权重, Some w_pre <= Some w_p *)
                simpl. 
                unfold Z_op_le in *. 
                lia.
              *** (* p 是 None *)
                simpl. unfold Z_op_le in *. assumption.
             ++ destruct (epath_weight g p) as [w_p | ];
                simpl; unfold Z_op_le in *; assumption.  
           **(* 边权重是 None *)
            destruct (epath_weight g p_pre_rest); destruct (epath_weight g p);
            simpl; unfold Z_op_le in *; try reflexivity; try assumption.
      * (* w 不在 vis_set -> w 即为切分点 *)
        exists w, (e :: nil).
        repeat split.
        -- exists (e :: nil), p.
           split; [simpl; reflexivity |].
           apply valid_epath_single; auto.
        -- apply valid_epath_single; assumption.
        -- intros p1 p2 x0 Hp1 Hp2 Heq Hval.
           destruct p1; [contradiction|].
           destruct p2; [contradiction|].
           simpl in Heq.
           injection Heq as _ Hrest.
           destruct p1; simpl in Hrest; discriminate.
        -- exact H_w_not_vis.
        -- unfold epath_weight; simpl.
          (* destruct (weight g e) as [we|]. *)
          destruct (weight g e) as [we|] eqn:H_we; [| simpl; try apply Z_op_le_none].
          destruct (fold_right Z_op_plus (Some 0) (map (weight g) p)) as [wp|] eqn:H_wp.
          ++ (* weight p = Some wp *)
            simpl. unfold Z_op_le.
            pose proof (valid_epath_non_neg _ _ _ _ H_path_w H_wp) as H_nonneg.
            lia.
          ++ (* weight p = None *)
            simpl. unfold Z_op_le. tauto.
          ++ (* weight e = None *)
            simpl. unfold Z_op_le.
            reflexivity.
    + (* u 不在 vis_set -> u 自身为切分点 *)
      exists u, nil.
      repeat split.
      -- exists nil, (e :: p). 
         split; [simpl; reflexivity |]. 
         apply valid_epath_empty.
      -- apply is_epath_through_vset_nil. auto.
      -- intros p1 p2 x Hp1 Hp2 Heq Hval.
         destruct p1; [contradiction | simpl in Heq; discriminate].
      -- exact H_u_not_vis.
      --
        unfold epath_weight at 1; simpl.
        destruct (epath_weight g (e :: p)) as [w_total | ] eqn:H_wt.
        ++
          simpl. unfold Z_op_le.
          assert (H_valid_total: valid_epath g u (e :: p) v_end).
           { eapply valid_epath_cons; eauto. }
          pose proof (valid_epath_non_neg _ _ _ _ H_valid_total H_wt).
          lia.
        ++ simpl. unfold Z_op_le. auto.
Qed.

Lemma greedy_choice_lemma:
  forall (u: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 前提：循环不变量成立 *)
    (forall v, v ∈ visited -> min_value_weight_epath g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_value_weight_epath_in_vset g src v visited (dist v)) ->
    (* u 是未访问顶点中 dist 值最小的 *)
    ~ u ∈ visited ->
    dist u <> None ->
    (forall v, ~ v ∈ visited -> dist v <> None -> Z_op_le (dist u) (dist v)) ->
    (* 结论：dist[u] 是最终的最短距离 *)
    min_value_weight_epath g src u (dist u).
Proof.
  intros u_target vis_set d_map H_vis_ok H_unvis_ok H_u_not_vis H_u_some H_u_is_min.

  pose proof (H_unvis_ok u_target H_u_not_vis) as H_u_status.
  unfold min_value_weight_epath_in_vset in H_u_status.
  unfold min_value_of_subset_with_default in H_u_status.

  destruct H_u_status as [H_path_exists | H_path_none].

  (* dist u = Some *)
  -
    destruct H_path_exists as [H_struct_u H_val_u].
    destruct H_struct_u as [p_best [H_p_thru_vis H_p_weight_is_dist]].

    left.
    split.

    {
      (* 先证明分割点的存在性
          分割点指的是路径上第一个离开 visited 集合的点 *)
      exists p_best. (* 当前 p_best 是 epath thru vset to u*)
      split.

      2: { 
        (* 证明 p_best 的长度就是记录的 dist u 的长度 *)
        exact H_p_weight_is_dist. }

      (* 证明 p_best 确实是 src 到 u 的全局最短路径*)
      destruct H_p_thru_vis as [H_is_thru _].
      destruct H_is_thru.
      split.
      + exact H.
      +
        intros p_any H_p_any_valid.
        rewrite H_p_weight_is_dist.

        (* 开始反证链条 *)
        pose proof (greedy_cut p_any u_target vis_set H_p_any_valid H_u_not_vis) as H_cut.
        destruct H_cut as [v [p_pre [H_pre_path [H_pre_thru_vis [H_v_not_vis H_weight_mono]]]]].
        pose proof (H_unvis_ok v H_v_not_vis) as H_v_opt.
        destruct (d_map v) eqn:H_dist_v.

        (* v 是 p_any 的分割点，p_any 终点是 u_target *)

        - (* 如果 dist v = Some z *)
          destruct H_v_opt as [H_v_exists | H_v_none].
          * (* 正常情况，v 能走到 *)
            destruct H_v_exists as [H_v_struct _].
            destruct H_v_struct as [p_v [H_pv_min H_pv_eq]].
            destruct H_pv_min as [_ H_min_forall].
            specialize (H_min_forall p_pre H_pre_thru_vis).
              
            assert (H_greedy: Z_op_le (d_map u_target) (d_map v)).
            { apply H_u_is_min; [exact H_v_not_vis | rewrite H_dist_v; congruence]. }
            
            (* 串联不等式 *)
            eapply Z_op_le_trans with (y := d_map v). { exact H_greedy. }
            rewrite H_dist_v. rewrite <- H_pv_eq.
            eapply Z_op_le_trans with (y := epath_weight g p_pre). { exact H_min_forall. }
            exact H_weight_mono.

          * (* 异常情况，v 走不到 *)
            destruct H_v_none as [_ H_dist_is_none].
            congruence.
        
        - (* 如果 dist v = None *)
          destruct H_v_opt as [H_v_exists | H_v_none].
          *
            destruct H_v_exists as [H_v_struct _].
            destruct H_v_struct as [p_v [H_pv_min H_pv_eq]].
            destruct H_pv_min as [H_pv_thru _].
            destruct H_pv_thru as [H_pv_valid _].
            (* 对 p_v 的权重进行拆解 *)
            destruct (epath_weight g p_v) eqn:H_pw_pv.
            -- (* 如果权重是 Some z，则 Some z = None，直接矛盾 *)
              congruence.
            -- (* 如果权重是 None，合法路径 pv 权重不为 None *)
              pose proof (valid_epath_not_none src p_v v H_pv_valid) as H_not_none.
              contradiction.

          *
          destruct H_v_none as [H_no_path_logic _].
          specialize (H_no_path_logic p_pre H_pre_thru_vis).
          
          (* 对 p_pre 的权重进行拆解 *)
          destruct (epath_weight g p_pre) eqn:H_pw_pre.
          -- (* 如果权重是 Some z *)
            unfold Z_op_le in H_no_path_logic. 
            contradiction.
          -- (* 如果权重是 None，合法路径 p_v 权重不为 None *)
            destruct H_pre_thru_vis as [H_pre_valid _].
            pose proof (valid_epath_not_none src p_pre v H_pre_valid) as H_not_none.
            contradiction.
    }
    { exact H_val_u. }

  (* dist u = None *)
  -
    destruct H_path_none as [_ H_is_none].
    rewrite H_is_none in H_u_some.
    congruence.
Qed.

Definition greedy_choice_correct (s: St) (u: V): Prop :=
  unvisited s u ->
  (forall v, unvisited s v -> Z_op_le (s.(dist) u) (s.(dist) v)) ->
  min_value_weight_epath g src u (s.(dist) u) \/ dist s u = None.

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
    apply (greedy_choice_lemma u (visited s) (dist s)).
      + apply H_vis_final.
      + apply H_unvis_opt.
      + destruct H_unvisited; assumption.
      + rewrite H_dist_val. congruence.
      + (* u 是距离 s 最小的*)
        rewrite H_dist_val.
        intros v H_v_not_vis H_v_dist_some.
        apply H_minimal.
        split.
        *
          pose proof (H_unvis_opt v H_v_not_vis) as H_opts.
          unfold min_value_weight_epath_in_vset, min_value_of_subset_with_default in H_opts.
          destruct H_opts as [H_some | H_none].
          --
            destruct H_some as [H_min_struct _].
            unfold min_value_of_subset in H_min_struct.
            destruct H_min_struct as [p_v [H_pv_thru _]].
            destruct H_pv_thru as [H_pv_valid _].
            destruct H_pv_valid as [H_pv_valid_raw _].
            apply valid_epath_reachable in H_pv_valid_raw.
            destruct (eq_dec src v).
            ++ subst. rewrite e in valid_src. exact valid_src.
            ++ apply reachable_vvalid in H_pv_valid_raw; [tauto | assumption].
          --
            destruct H_none as [_ H_is_none].
            congruence.
        * exact H_v_not_vis.
  -
    unfold unvisited_dist_optimal in H_unvis_opt.
    right.
    reflexivity.
Qed.

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
  unfold select_min_vertex.
  set (Pa := (fun (s : St) (u : V) => 
              min_object_of_subset Z_op_le
                (fun v : V => unvisited s v) (dist s) u)).
  apply Hoare_conseq_post with (Q2 := fun u s => Pa s u /\ loop_invariant s).
  2:{ apply Hoare_get. }
  intros u s H. destruct H.
  split; [auto|].
  unfold select_min_vertex_prop_wrap.
  split; unfold Pa in H.
  - apply min_object_legal in H; auto.
  - apply min_object_sound; auto.
Qed.

Lemma visit_fact (v: V) P1:
  Hoare P1 (visit v) (fun _ s => exists s', (s.(dist) = s'.(dist)) 
                        /\ (s.(visited) == s'.(visited) ∪ Sets.singleton v) 
                        /\ P1 s').
Proof.
  unfold visit.
  eapply Hoare_conseq_post; [| apply Hoare_update].
  intros u s2. simpl. intros.
  destruct H as [s1 H].
  exists s1.
  destruct H as [Hupdtae HP1].
  subst s2.
  split; [|split]; simpl; easy.
Qed.

Lemma Z_op_plus_zero_r:
  forall z, Z_op_plus z (Some 0) = z.
Proof. 
  intros.
  unfold Z_op_plus.
  destruct z.
  - replace (z + 0) with z by lia.
    reflexivity.
  - reflexivity.
Qed.

Lemma path_weight_concat_iff_Z_op_plus:
  forall (p1 p2 : P) (u v : V),
    (path_weight g (concat_path p1 p2)) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros.
  unfold path_weight.
  rewrite concat_path_edge.
  rewrite map_app.
  apply Zlist_sum_app.
Qed.

(* 根据dist s v的最优性，dist s v <= dist s u + weight g e 恒成立 *)
Lemma min_value_weight_epath_prop (s : St) (u v : V) (e : E):
  (step_aux g e u v) ->
  (min_value_weight_epath g src u (dist s u)) ->
  (min_value_weight_epath g src v (dist s v)) ->
  (le_min Z_op_le (dist s v) (Z_op_plus (dist s u) (weight g e)) = dist s v).
Proof.
  intros Hstep Hdist_u Hdist_v.
  unfold min_value_weight_epath, min_value_of_subset_with_default in Hdist_u, Hdist_v.

  destruct Hdist_u as [[H_ex_u H_min_u] | [H_empty_u H_none_u]];
  destruct Hdist_v as [[H_ex_v H_min_v] | [H_empty_v H_none_v]].

  - (* u 可达 (Some), v 可达 (Some) *)
    destruct H_ex_u as [p_u [H_valid_u H_weight_u]].
    destruct H_valid_u as [H_pu_valid _].
    pose proof (valid_epath_snoc g src p_u u v e H_pu_valid Hstep) as H_new_valid.

    destruct H_ex_v as [p_v [[H_pv_valid H_pv_weight] H_v_min]].
    specialize (H_pv_weight (p_u ++ e :: nil)).
    specialize (H_pv_weight H_new_valid).

    (* 将不等式转化为 dist s v <= dist s u + weight e *)
    rewrite epath_weight_app_assoc in H_pv_weight.
    rewrite H_v_min in H_pv_weight.
    rewrite H_weight_u in H_pv_weight.
    (* epath_weight [e] = weight e *)
    assert (H_edge_w: epath_weight g (e :: nil) = weight g e).
    {
      unfold epath_weight; simpl.
      unfold Z_op_plus.
      destruct (weight g e) eqn:He.
      - f_equal. lia.
      - reflexivity.
    }

    rewrite H_edge_w in H_pv_weight.
    unfold le_min.
    destruct (le_total (dist s v) (Z_op_plus (dist s u) (weight g e))) eqn:H_le.
    + reflexivity.
    + apply Z_op_le_antisym; assumption.
  
  - (* u 可达 (Some), v 不可达 (None) *)
    destruct H_ex_u as [p_u [H_valid_u_struct H_weight_u]].
    destruct H_valid_u_struct as [H_pu_valid _].

    pose proof (valid_epath_snoc g src p_u u v e H_pu_valid Hstep) as H_new_valid.
    specialize (H_empty_v (p_u ++ e :: nil)).
    specialize (H_empty_v H_new_valid).
    rewrite epath_weight_app_assoc in H_empty_v.
    rewrite H_weight_u in H_empty_v.

    assert (H_edge_w: epath_weight g (e :: nil) = weight g e).
    {
      unfold epath_weight; simpl. unfold Z_op_plus.
      destruct (weight g e) eqn:He.
      - f_equal. lia.
      - reflexivity.
    }

    rewrite H_edge_w in H_empty_v.
    simpl in H_empty_v.

    destruct (weight g e) eqn:Hwe.
    2:{
      pose proof (weight_defined _ _ _ Hstep).
      congruence.
    }
    rewrite <- H_weight_u in H_empty_v.

    assert (H_pu_some: epath_weight g p_u <> None).
    { apply valid_epath_not_none with (u:=src) (v:=u); assumption. }

    destruct (epath_weight g p_u) eqn:Hw_pu.
    2:{ contradiction. }
    unfold Z_op_plus in H_empty_v.
    contradiction.
  
  - (* u 不可达 (None), v 可达 (Some) *)
    rewrite H_none_u. simpl.
    unfold le_min.
    destruct (le_total (dist s v) None) as [H_le | H_ge].
    + reflexivity.
    + simpl in H_ge. destruct (dist s v) eqn:Hdv; [contradiction| reflexivity].
  
  - (* u 不可达 (None), v 不可达 (None) *)
    rewrite H_none_u. simpl.
    rewrite H_none_v.
    unfold le_min.
    destruct (le_total None None); reflexivity.
Qed.

(* 依据dist s v是经过vset的最优性，那么不论u如何，dist s v <= dist s u + weight g e 恒成立 *)
Lemma min_value_weight_epath_in_vset_prop (s : St) (u v : V) (e : E):
  (visited s u) ->
  (step_aux g e u v) ->
  (min_value_weight_epath_in_vset g src v (visited s) (dist s v)) ->
  (min_value_weight_epath_in_vset g src u (visited s) (dist s u)) ->
  (le_min Z_op_le (dist s v) (Z_op_plus (dist s u) (weight g e)) = dist s v).
Proof.
  intros Hvis Hstep Hdist_v H_opt_u.
  unfold min_value_weight_epath_in_vset, min_value_of_subset_with_default in H_opt_u.

  destruct H_opt_u as [H_some_u | [H_empty_u H_none_u]].

  - (* dist s u = Some d *)
    destruct H_some_u as [H_ex_u _].
    destruct H_ex_u as [p_u [H_u_obj H_weight_u]].
    unfold min_object_of_subset in H_u_obj.
    destruct H_u_obj as [H_valid_u H_u_is_min].
    pose (p_new := p_u ++ e :: nil).
    assert (H_valid_new: is_epath_through_vset g src p_new v (visited s)).
    {
      unfold p_new.
      eapply is_epath_through_vset_app with (m := u).
      - exact H_valid_u. (* p_u 合法 *)
      - apply is_epath_through_vset_single. exact Hstep. (* 单步合法 *)
      - exact Hvis. (* u 在 visited 中 *)
    }

    assert (H_weight_new: epath_weight g p_new = Z_op_plus (dist s u) (weight g e)).
    {
      unfold p_new.
      rewrite epath_weight_app_assoc.
      rewrite H_weight_u.
      assert (H_single: epath_weight g (e :: nil) = weight g e).
      { unfold epath_weight; simpl; unfold Z_op_plus. destruct (weight g e); auto. f_equal; lia. }
      rewrite H_single.
      reflexivity.
    }

    unfold min_value_weight_epath_in_vset, min_value_of_subset_with_default in Hdist_v.
    destruct Hdist_v as [H_ex_v | [H_empty_v H_none_v]].
    
    + (* dist s v = Some *)
      destruct H_ex_v as [H_v_exists _].
      destruct H_v_exists as [p_v [H_v_obj H_v_weight_eq]].
      unfold min_object_of_subset in H_v_obj.
      destruct H_v_obj as [_ H_v_is_min].
      specialize (H_v_is_min p_new H_valid_new).
      rewrite H_v_weight_eq in H_v_is_min.
      rewrite H_weight_new in H_v_is_min.
      unfold le_min.
      destruct (le_total (dist s v) (Z_op_plus (dist s u) (weight g e))).
      * reflexivity.
      * apply Z_op_le_antisym; assumption.
    
    + (* dist s v = None *)
      specialize (H_empty_v p_new H_valid_new).
      rewrite H_weight_new in H_empty_v.
      
      destruct (dist s u) eqn:Hu.
      *
        destruct (weight g e) eqn:Hwe.
        -- simpl in H_empty_v. contradiction. 
        -- pose proof (weight_defined _ _ _ Hstep). congruence.
      *
        destruct H_valid_u as [H_valid_u_flat _].
        apply valid_epath_not_none in H_valid_u_flat.
        rewrite H_weight_u in H_valid_u_flat.
        congruence.
  
  - (* dist s u = None *)
    rewrite H_none_u. simpl.
    unfold le_min.
    destruct (le_total (dist s v) None).
    + reflexivity.
    + destruct (dist s v); [contradiction|reflexivity].
  
  Unshelve.
  apply g_valid.
Qed. 

Lemma relax_fact (u: V) (e : E):
  Hoare
    (fun s' => loop_invariant s' /\ visited s' u /\ (exists v, step_aux g e u v))
    (relax_edge u e)
    (fun _ s => visited s u).
Proof.
  unfold relax_edge.
  hoare_auto. intro_state. 
  eapply Hoare_conseq_post; [| apply Hoare_update].
  intros. simpl in *.
  destruct H as [? [? [? [? ?]]]].
  destruct H0 as [s' [? ?]]. subst s0.
  destruct H2 as [? [? [? ?]]].
  subst s. simpl. auto.
Qed.

Lemma no_reachable_not_exists_e (u v : V):
  reachable src u -> ~reachable src v -> forall e, ~step_aux g e u v.
Proof.
    intros H_reach_u H_not_reach_v e0 H_step.
    apply H_not_reach_v.
    eapply reachable_step_reachable.
    - exact H_reach_u.
    - exists e0. exact H_step.
Qed.

(* While scanning outgoing edges, only settled distances are final.
   Each finite label is witnessed by a path through the settled vertices. *)
Definition witnessed (s : St) :=
  forall v w, dist s v = Some w -> exists p,
    is_epath_through_vset g src p v (visited s) /\ epath_weight g p = Some w.

Definition edge_bound (s : St) x e y :=
  Z_op_le (dist s y) (Z_op_plus (dist s x) (weight g e)).

Record labels_ok (s : St) : Prop := {
  labels_final : visited_dist_final s;
  labels_witness : witnessed s;
  labels_zero : source_dist_zero s;
  labels_src : visited s src;
  labels_valid : validity_constraint s;
  labels_reach : reachable_prop s
}.

Definition ready (s : St) :=
  labels_ok s /\ forall x e y, visited s x -> step_aux g e x y -> edge_bound s x e y.

Lemma minimum_lower (X : list E -> Prop) d :
  min_value_of_subset_with_default Z_op_le X (epath_weight g) None d ->
  forall p, X p -> Z_op_le d (epath_weight g p).
Proof.
  intros [[[q [[_ Hmin] <-]] _] | [Hmin ->]] p Hp; auto.
Qed.

Lemma single_weight e : epath_weight g (e :: nil) = weight g e.
Proof. unfold epath_weight; simpl; apply Z_op_plus_zero_r. Qed.

Lemma ready_invariant s : ready s -> loop_invariant s.
Proof.
  intros [[Hfinal Hwit Hz Hsrc Hvalid Hr] Hedges].
  split; [exact Hfinal|]. split; [|split; [exact Hz|split; assumption]].
  intros v Hout.
  assert (Hlower : forall p, is_epath_through_vset g src p v (visited s) ->
                  Z_op_le (dist s v) (epath_weight g p)).
  { intros p [Hp Hinter].
    destruct (valid_epath_inv_n1 g src p v Hp) as [[-> Heq]|[q [x [e [-> [Hq He]]]]]].
    - subst. contradiction.
    - assert (Hx : visited s x).
      { destruct q as [|first q]. - apply valid_epath_nil_inv in Hq. subst; auto.
        - apply (Hinter (first :: q) (e :: nil) x); [discriminate|discriminate|reflexivity|exact Hq]. }
      rewrite epath_weight_app_assoc, single_weight.
      eapply Z_op_le_trans; [exact (Hedges x e v Hx He)|].
      apply Z_op_plus_mono; [eapply minimum_lower; [apply Hfinal; exact Hx|exact Hq]|apply Z_op_le_refl]. }
  destruct (dist s v) as [w|] eqn:Hd.
  - destruct (Hwit _ _ Hd) as [p [Hp Hw]]. left. split; [|apply Z_op_le_none_r].
    exists p. split; [split; [exact Hp|rewrite Hw; exact Hlower]|exact Hw].
  - right; auto.
Qed.

Lemma selected_finite s u :
  loop_invariant s -> ~ unvisited_no_reachable s ->
  select_min_vertex_prop_wrap u s -> dist s u <> None.
Proof.
  intros [Hfinal [Hopt [Hz [Hv Hr]]]] Hguard [_ Hmin] Hinf.
  apply Hguard. intros dest [_ Hout] Hreachable.
  apply reachable_valid_epath in Hreachable as [p Hp].
  destruct (greedy_cut p dest (visited s) Hp Hout)
    as [x [q [_ [Hq [Hx _]]]]].
  assert (Hvalid : vvalid g x).
  { destruct (classic (src = x)) as [<-|Hne]; auto.
    eapply reachable_basic.reachable_vvalid; [exact Hne|].
    eapply valid_epath_reachable; apply Hq. }
  specialize (Hmin x (conj Hvalid Hx)).
  rewrite Hinf in Hmin. apply Z_op_none_le_iff in Hmin.
  pose proof (minimum_lower _ _ (Hopt x Hx) q Hq) as Hbound.
  rewrite Hmin in Hbound. apply Z_op_none_le_iff in Hbound.
  exact (valid_epath_not_none _ _ _ (proj1 Hq) Hbound).
Qed.

Definition scanning (old : V -> Prop) (u : V) (done : E -> Prop) (s : St) :=
  labels_ok s /\ visited s == old ∪ [u] /\
  forall x e y, old x \/ (x = u /\ done e) -> step_aux g e x y -> edge_bound s x e y.

Lemma start_scan s u :
  ready s -> ~ unvisited_no_reachable s -> select_min_vertex_prop_wrap u s ->
  scanning (visited s) u ∅ (mkSt (visited s ∪ [u]) (dist s)).
Proof.
  intros Hready Hguard Hsel. pose proof (ready_invariant s Hready) as Hinv.
  pose proof (selected_finite s u Hinv Hguard Hsel) as Hfinite.
  destruct (greedy_choice_correct_prop s u Hinv (proj1 Hsel) (proj2 Hsel))
    as [Hbest | Hinf]; [|contradiction].
  destruct Hready as [[Hfinal Hwit Hz Hsrc Hv [Hr Hnone]] Hedges].
  split; [constructor|split].
  - intros x [Hold | Heq]; [auto | change (u = x) in Heq; subst; exact Hbest].
  - intros x w Hd. destruct (Hwit x w Hd) as [p [Hp Hw]].
    exists p. split; [|exact Hw]. eapply is_epath_through_vset_subset; [exact Hp|].
    intros y Hy. left; exact Hy.
  - exact Hz.
  - left; exact Hsrc.
  - intros x [Hold | Heq]; [auto | change (u = x) in Heq; subst; apply Hsel].
  - split; [|exact Hnone]. intros x [Hold | Heq]; [auto|].
    change (u = x) in Heq. subst. apply NNPP. intro Hnot. auto.
  - reflexivity.
  - intros x e y [Hold | [_ Hempty]] He; [apply Hedges; assumption|contradiction].
Qed.

Definition relaxed (s : St) u e y :=
  mkSt (visited s) (y !-> le_min Z_op_le (dist s y)
                          (Z_op_plus (dist s u) (weight g e)); dist s).

Lemma scan_edge old u done s e y :
  scanning old u done s -> step_aux g e u y ->
  scanning old u (done ∪ [e]) (relaxed s u e y).
Proof.
  intros [[Hfinal Hwit Hz Hsrc Hv [Hr Hnone]] [Hset Hclosed]] He.
  assert (Hu : visited s u) by (apply Hset; right; reflexivity).
  assert (Hfinite : dist s u <> None).
  { destruct (Hfinal u Hu) as [[[p [[Hp _] Hw]] _]|[Hempty ->]].
    - rewrite <- Hw. exact (valid_epath_not_none _ _ _ Hp).
    - destruct (reachable_valid_epath g src u (Hr u Hu)) as [p Hp].
      specialize (Hempty p Hp). apply Z_op_none_le_iff in Hempty.
      exfalso. exact (valid_epath_not_none _ _ _ Hp Hempty). }
  destruct (dist s u) as [w|] eqn:Hw; [|contradiction].
  destruct (Hwit u w Hw) as [p [Hp Hpw]].
  set (candidate := Z_op_plus (Some w) (weight g e)).
  assert (Hpath : is_epath_through_vset g src (p ++ e :: nil) y (visited s)).
  { eapply is_epath_through_vset_app; [exact Hp|apply is_epath_through_vset_single; exact He|exact Hu]. }
  assert (Hweight : epath_weight g (p ++ e :: nil) = candidate).
  { rewrite epath_weight_app_assoc, single_weight, Hpw. reflexivity. }
  set (next := relaxed s u e y).
  assert (Hat : dist next y = le_min Z_op_le (dist s y) candidate).
  { unfold next, relaxed; simpl. unfold t_set. destruct (equiv_dec y y) as [Hy|Hne];
      [rewrite Hw; reflexivity|exfalso; apply Hne; reflexivity]. }
  assert (Haway : forall x, y <> x -> dist next x = dist s x).
  { intros x Hne. unfold next, relaxed; simpl. unfold t_set.
    destruct (equiv_dec y x); [contradiction|reflexivity]. }
  assert (Hdecrease : forall x, Z_op_le (dist next x) (dist s x)).
  { intro x. destruct (classic (y = x)) as [<-|Hne].
    - rewrite Hat. unfold le_min. destruct (le_total (dist s y) candidate); auto using Z_op_le_refl.
    - rewrite Haway by auto. apply Z_op_le_refl. }
  assert (Hkeep : forall x, visited s x -> dist next x = dist s x).
  { intros x Hx. destruct (classic (y = x)) as [<-|Hne]; [|auto].
    rewrite Hat. apply min_r. rewrite <- Hweight.
    exact (minimum_lower _ _ (Hfinal y Hx) _ (proj1 Hpath)). }
  split; [constructor|split].
  - intros x Hx. change (min_value_weight_epath g src x (dist next x)).
    rewrite Hkeep by exact Hx. auto.
  - intros x z Hd. change (dist next x = Some z) in Hd.
    destruct (classic (y = x)) as [<-|Hne].
    + rewrite Hat in Hd. unfold le_min in Hd. destruct (le_total (dist s y) candidate).
      * exact (Hwit y z Hd).
      * exists (p ++ e :: nil). split; [exact Hpath|congruence].
    + rewrite Haway in Hd by auto. exact (Hwit x z Hd).
  - change (dist next src = Some 0). rewrite Hkeep by auto. exact Hz.
  - exact Hsrc.
  - exact Hv.
  - split; [exact Hr|]. intros x Hnot. change (dist next x = None).
    rewrite Haway; [auto|]. intro Heq. subst. apply Hnot.
    eapply valid_epath_reachable. exact (proj1 Hpath).
  - exact Hset.
  - intros x f z [Hold | [-> [Hdone | Hnew]]] Hf.
    + unfold edge_bound. change (Z_op_le (dist next z) (Z_op_plus (dist next x) (weight g f))).
      rewrite (Hkeep x) by (apply Hset; left; exact Hold).
      eapply Z_op_le_trans; [apply Hdecrease|apply Hclosed; auto].
    + unfold edge_bound. change (Z_op_le (dist next z) (Z_op_plus (dist next u) (weight g f))).
      rewrite (Hkeep u) by exact Hu. eapply Z_op_le_trans; [apply Hdecrease|apply Hclosed; auto].
    + change (e = f) in Hnew. subst f.
      destruct (graph_basic.step_aux_unique g e u y u z g_valid He Hf) as [_ <-].
      change (Z_op_le (dist next y) (Z_op_plus (dist next u) (weight g e))).
      rewrite (Hkeep u) by exact Hu. rewrite Hw, Hat. fold candidate.
      unfold le_min. destruct (le_total (dist s y) candidate); auto using Z_op_le_refl.
Unshelve. all: assumption.
Qed.

Definition selected s u := ready s /\ ~ unvisited_no_reachable s /\ select_min_vertex_prop_wrap u s.

Lemma select_for_scan :
  Hoare (fun s => ~ unvisited_no_reachable s /\ ready s)
    select_min_vertex (fun u s => selected s u).
Proof.
  intros s u t [Hg Hready] [Hmin <-]. split; [exact Hready|]. split; assumption.
Qed.

Lemma process_vertex_holds_inv u :
  Hoare (fun s => selected s u) (process_vertex u) (fun _ s => ready s).
Proof.
  intros old a last [Hready [Hg Hmin]] [[] [first [Hvisit Hrun]]].
  change (first = mkSt (visited old ∪ [u]) (dist old)) in Hvisit. subst first.
  set (edges := fun e => exists y, step_aux g e u y).
  assert (Hloop : Hoare (scanning (visited old) u ∅)
                 (forset edges (relax_edge u))
                 (fun _ => scanning (visited old) u edges)).
  { apply Hoare_forset.
    - intros d1 d2 Hd s t <-. unfold scanning.
      assert (Hmember : forall e, d1 e <-> d2 e) by (intro; apply Hd).
      split.
      all: intros [Hl [Hs Hb]]; split; [exact Hl|split; [exact Hs|]].
      all: intros x e y Hx He; apply Hb; [specialize (Hmember e); tauto|exact He].
    - intros done e _ _ _ s b t Hscan [[] [s1 [[_ Hsame] [y [s2 [[He Hsame'] Hupd]]]]]].
      subst s1 s2. change (t = relaxed s u e y) in Hupd. subst t.
      exact (scan_edge _ _ _ _ _ _ Hscan He). }
  destruct (Hloop _ _ _ (start_scan old u Hready Hg Hmin) Hrun) as [Hl [Hs Hb]].
  split; [exact Hl|]. intros x e y Hx He. apply Hb; [|exact He].
  apply Hs in Hx as [Ho|Heq]; [auto|]. change (u = x) in Heq. subst.
  right; split; [reflexivity|exists y; exact He].
Qed.

(** ===== 正确性规范 ===== *)

(** 健全性：记录的距离是真实的最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall v w, vvalid g v -> s.(dist) v = w -> min_value_weight_epath g src v w.

(** 完备性：真实的最短距离被正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall v w, vvalid g v -> min_value_weight_epath g src v w -> s.(dist) v = w.

(** 完整正确性：健全性 + 完备性 *)
Definition distance_correct (s: St): Prop :=
  distance_soundness s /\ distance_completeness s.

(** 每轮开始时 ready 蕴含原循环不变量。选择距离最小的未访问顶点后，
    逐条松弛其有向出边，处理完毕时恢复 ready。退出分支给出最终距离。 *)

Definition continue_bind_aux (a : CntOrBrk unit unit): St -> Prop :=
  match a with
  | by_continue _=> fun s => ready s
  | by_break _ => fun _ => True
  end.

(* ✅ *)
Lemma continue_holds_invariant:
  Hoare
  (fun s : St => ready s)
  (x <- choice
      (assume (fun s => ~unvisited_no_reachable s);;
        u <- select_min_vertex;; 
        process_vertex u;;
        ret (by_continue tt))
      (assume (fun s => unvisited_no_reachable s);;
        ret (by_break tt));;
    continue_case x)
  (fun (_ : unit) (s : St) => ready s).
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
  apply Hoare_bind with (Q := fun u s => selected s u).
    1:{ apply select_for_scan. }
  intros u. (* process 取出的顶点 *)
  apply Hoare_bind with (Q := fun _ s => ready s).
  1:{ apply process_vertex_holds_inv. }
  intros _.
  apply Hoare_ret'.
  intros. simpl. auto.
Qed.

Definition break_bind_aux (a : CntOrBrk unit unit): St -> Prop :=
  match a with
  | by_continue _=> fun _ => True
  | by_break _ => fun s => ready s /\ unvisited_no_reachable s
  end.

Lemma no_reachable_iff_min_value_weight_epath_None:
  forall u, ~reachable src u <-> min_value_weight_epath g src u None.
Proof. 
  intros u.
  unfold min_value_weight_epath; split.
  (* ~reachable -> None *)
  - intro H_unreachable.
    apply min_default_default.
    intros p H_valid.
    apply valid_epath_reachable in H_valid.
    contradiction.
  (* None -> ~reachable *)
  - intro H_min.
    intro H_reach. (* 反证 *)
    apply reachable_valid_epath in H_reach.
    destruct H_reach as [p H_valid].
    unfold min_value_weight_epath, min_value_of_subset_with_default in H_min.
    destruct H_min as [[H_ex_min _] | [H_empty _]].
    (* ∃path为None --- *)
    + destruct H_ex_min as [p_min [[H_valid_min _] H_weight_eq_none]].
      apply valid_epath_not_none in H_valid_min.
      congruence.
    (* 集合为空 *)
    + specialize (H_empty p H_valid).
      destruct (epath_weight g p) eqn:Heq_wp. 
      * simpl in H_empty.
        contradiction.
      * apply valid_epath_not_none in H_valid.
        congruence.
Qed.

Lemma visited_unvisited_by_classic: 
  forall s u, vvalid g u -> visited s u \/ unvisited s u.
Proof. intros. unfold unvisited. tauto. Qed.

Lemma min_value_weight_epath_inj:
  forall u w w', 
    min_value_weight_epath g src u w ->
    min_value_weight_epath g src u w' ->
    w = w'.
Proof.
  intros u w w' H1 H2.
  unfold min_value_weight_epath in *.
  (* Search TotalOrder Z_op_le. *)
  eapply min_default_unique; eauto.
  constructor.
  - intros [x|]; simpl.
    + apply Z.le_refl.
    + trivial.
  - intros [x|] [y|] [z|]; simpl; intros Hxy Hyz; try trivial; try contradiction. lia.
  - intros [x|] [y|]; simpl; intros Hxy Hyx; try trivial; try contradiction. f_equal. lia.
  - intros [x|] [y|]; simpl.
    + destruct (Z_le_gt_dec x y).
      * left; assumption.
      * right; apply Z.lt_le_incl; lia.
    + left; trivial.
    + right; trivial.
    + left; trivial.
Qed.

(* TODO *)
Lemma distance_correct_aux (s : St):
  unvisited_no_reachable s ->
  loop_invariant s ->
  distance_correct s.
Proof.
  intros.
  destruct H0 as [? [? [? [? ?]]]].
  unfold visited_dist_final in H0.
  unfold unvisited_dist_optimal in H1.
  unfold source_dist_zero in H2.
  unfold validity_constraint in H3.
  constructor.
  - unfold distance_soundness. intros.
    unfold unvisited_no_reachable in H.
    pose proof visited_unvisited_by_classic s v H5.
    rewrite <- H6.
    destruct H7.
    + apply (H0 v H7).
    + pose proof H v H7.
      destruct H4.
      pose proof H9 v H8.
      apply no_reachable_iff_min_value_weight_epath_None in H8.
      rewrite H10.
      auto.
      (* termination_condition and no_reachable -> dist s v = min_value_weight_epath = None *)
  - unfold distance_completeness. intros.
    unfold unvisited_no_reachable in H.
    pose proof visited_unvisited_by_classic s v H5.
    destruct H7.
    + pose proof H0 v H7.
      apply (min_value_weight_epath_inj v); try auto.
    + pose proof H v H7.
      destruct H4.
      pose proof H9 v H8.
      apply no_reachable_iff_min_value_weight_epath_None in H8.
      rewrite H10.
      apply (min_value_weight_epath_inj v); try auto.
    (* 这里主要证明min_value_weight_epath这个函数是一个单射 *)
Qed.

(* ✅ *)
Lemma termination_implies_correctness:
  Hoare
  (fun s : St => ready s)
  (x <- choice
      (assume (fun s => ~unvisited_no_reachable s);;
        u <- select_min_vertex;; 
        process_vertex u;;
        ret (by_continue tt))
      (assume (fun s => unvisited_no_reachable s);;
        ret (by_break tt));;
    break_case x)
  (fun (_ : unit) (s : St) => ready s /\ unvisited_no_reachable s).
Proof.
  apply Hoare_bind with (Q := break_bind_aux).
  2:{ intros. 
      destruct a; unfold break_case.
      - apply Hoare_empty.
      - apply Hoare_ret'; intros.
        apply H. }
  hoare_auto. (* 怎么突然又有了🤔 *)
  1:{ apply Hoare_bind with (Q := fun u s => selected s u).
    1:{ apply select_for_scan. }
      intros u. (* process 取出的顶点 *)
      apply Hoare_bind with (Q := fun _ s => ready s).
      1:{ apply process_vertex_holds_inv. }
      intros _.
      apply Hoare_ret'.
      intros. simpl. auto. }
  simpl. destruct H.
  split; assumption.
Qed.


(*证明empty_path是nil*)
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
  
Lemma dist_initSt_src_zero : dist initSt src = Some 0.
Proof.
  simpl.
  destruct eq_dec; [reflexivity | unfold complement, equiv in c]; tauto.
Qed.

Lemma path_through_empty_is_single_edge:
  forall (p : list E) (u v : V),
    u <> v ->
    valid_epath g u p v ->
    is_epath_through_vset g u p v ∅ ->
    exists e, p = e :: nil.
Proof.
  intros p u0 v0 Hneq Hvalid Hthrough.
  destruct p as [|e p'].
  - apply valid_epath_nil_inv in Hvalid. subst. contradiction.
  - destruct p' as [|e' p''].
    + exists e. reflexivity.
    + unfold is_epath_through_vset in Hthrough.
      destruct Hthrough as [_ Hcond].
      apply valid_epath_cons_inv in Hvalid.
      destruct Hvalid as [v_mid [Hstep Hvalid_rest]].
      specialize (Hcond (e::nil) (e'::p'') v_mid).
      
      (* 为了避免编号混乱，建议给 assert 起明确的名字 *)
      assert (Heq: e :: e' :: p'' = (e :: nil) ++ e' :: p'') by reflexivity.
      assert (Hnonil1: e :: nil <> nil) by discriminate.
      assert (Hnonil2: e' :: p'' <> nil) by discriminate.
      assert (Hval1: valid_epath g u0 (e :: nil) v_mid) by (apply valid_epath_single; auto).
      
      (* 按正确顺序应用参数 *)
      specialize (Hcond Hnonil1 Hnonil2 Heq Hval1).
      
      (* Hcond 现在的结论是 v_mid ∈ ∅，这是矛盾的 *)
      inversion Hcond.
Qed.

(* TODO *)
Lemma min_value_weight_epath_in_vset_empty (v : V):
  min_value_weight_epath_in_vset g src v [src] (dist initSt v) . (*不经过任何点的距离就是一开始的dist记录的距离；src-src -> 0=0; src-v -> None = None*)
Proof.
  unfold min_value_weight_epath_in_vset, min_value_of_subset_with_default.
  destruct (eq_dec v src) as [Heq | Hneq].
  - (* Case 1: v = src *)
    unfold equiv in Heq. subst v.
    (* 获取 initSt src = Some 0 的性质 *)
    rewrite dist_initSt_src_zero. 
    (* 证明 Some 0 是最小距离 *)
    left. split.
    + (* 存在性：构造空路径 nil *)
      exists nil.
      split.
      * (* 证明 nil 满足条件 *)
        unfold min_object_of_subset. split.
        -- apply is_epath_through_vset_nil. (* nil 总是通过任意集合 *)
        -- (* 证明最小性：0 <= 任意路径权重 *)
           intros p Hp.
           simpl. destruct (epath_weight g p) eqn:Hw; [| simpl; trivial].
           simpl. unfold Z_op_le.
           destruct Hp as [Hvalid _].
           eapply valid_epath_non_neg; eauto. (* 引用非负权引理 *)
      * reflexivity.
    + (* 默认值检查 *)
      simpl; trivial.
  - (* Case 2: v <> src *)
    unfold initSt; simpl.
    destruct (eq_dec v src); [contradiction |]. 
    
    set (Pred := fun (ow : option Z) => 
          (exists (e : E), step_aux g e src v /\ weight g e = ow) \/
          (ow = None /\ ~exists (e : E), step_aux g e src v)).
    assert (Heps: Pred (Coq.Logic.ClassicalEpsilon.epsilon (inhabits None) Pred)).
    {
      apply Coq.Logic.ClassicalEpsilon.epsilon_spec.
      destruct (classic (exists e, step_aux g e src v)).
      * destruct H as [e Hstep]. exists (weight g e). left. exists e. auto.
      * exists None. right. auto.
    }
    destruct Heps as [[e_edge [Hstep Hw_eq]] | [Hnone Hno_step]].

    + (* Subcase 2.1: Exists edge src -> v *)
      left. split.
      * exists (e_edge :: nil). split.
        -- unfold min_object_weight_epath_in_vset.
           split.
           ++ apply is_epath_through_vset_single; auto.
           ++ intros p' Hp'.
              destruct Hp' as [Hvalid_p' Hthru_p'].
              unfold epath_weight. simpl. rewrite Hw_eq. rewrite Z_op_plus_zero_r.

              (* Decompose path p' from the tail to analyze its structure *)
              destruct (valid_epath_inv_n1 g src p' v Hvalid_p') as [[Heq_nil _] | [p_pre [u [e_last [Heq_p [Hvalid_pre Hstep_last]]]]]].
              { 
                subst. 
                (* Hneq becomes v =/= v. contradiction might fail on notation, but congruence works. *)
                congruence. 
              }
              subst p'.
              destruct p_pre as [| e p_tail].
            { (* Case 1: p_pre is nil. Path is just [e_last] *)
               simpl. (* Simplifies nil ++ e_last :: nil to e_last :: nil *)
               
               apply valid_epath_nil_inv in Hvalid_pre. 
               subst u.
               
               (* Since graph is simple, the edge e_last (src->v) must be e_edge *)
               assert (e_last = e_edge). { eapply simple_graph; eauto. }
               subst e_last.
               
               (* 关键修正：利用 Hw_eq 将左边的 epsilon 替换为 weight *)
               rewrite <- Hw_eq.
               
               (* 处理列表求和产生的 +0 (如果有的话) *)
               try rewrite Z_op_plus_zero_r.
               
               (* 现在两边都是 weight g e_edge，可以使用自反性 *)
               apply Z_op_le_refl.
            }
            { (* p_pre 非空 *)
                 specialize (Hthru_p' (e :: p_tail) (e_last :: nil) u).
                 assert (e :: p_tail <> nil) by discriminate.
                 assert (e_last :: nil <> nil) by discriminate.
                 
                 (* 利用 eq_refl 规避 subst 导致的问题 *)
                 specialize (Hthru_p' H H0 eq_refl Hvalid_pre).
                 sets_unfold in Hthru_p'. subst u.

                 assert (e_last = e_edge). { eapply simple_graph; eauto. }
                 subst e_last.

                 (* 修复点 2：显式折叠 fold_right 为 epath_weight，以便 rewrite *)
                 change (fold_right Z_op_plus (Some 0) (map (weight g) ((e :: p_tail) ++ e_edge :: nil)))
                   with (epath_weight g ((e :: p_tail) ++ e_edge :: nil)).
                 
                 rewrite epath_weight_app_assoc.
                 rewrite <- Hw_eq.

                 (* 简化单边路径权重 *)
                 assert (Hsingle: epath_weight g (e_edge :: nil) = weight g e_edge).
                 { unfold epath_weight. simpl. apply Z_op_plus_zero_r. }
                 rewrite Hsingle.

                 (* 利用非负性 *)
                 destruct (epath_weight g (e :: p_tail)) as [wp |] eqn:Hwp.
                 ** destruct (weight g e_edge) as [we |] eqn:Hwe.
                    --- simpl. unfold Z_op_le.
                        pose proof (valid_epath_non_neg _ _ _ _ Hvalid_pre Hwp).
                        lia.
                    --- simpl. trivial.
                 ** simpl. destruct (weight g e_edge); simpl; trivial.
              }
        -- (* 分支 2: 证明路径权重等于 dist initSt v [cite: 482] *)
           unfold epath_weight; simpl.
           rewrite Z_op_plus_zero_r.
           rewrite Hw_eq. (* 权重即为 epsilon 选出的值 *)
           reflexivity.
      * (* 证明默认值部分：default <= n [cite: 59, 66] *)
        simpl. unfold Z_op_le. (* 显式展开序关系定义  *)
        destruct (ClassicalEpsilon.epsilon (inhabits None) Pred); auto.
    + (* Subcase 2.2: 不存在边 src -> v [cite: 541] *)
      rewrite Hnone.
      right. split; [| reflexivity].
      intros p' Hp'.
      destruct Hp' as [Hvalid_p' Hthru_p'].
      exfalso.
      destruct (valid_epath_inv_n1 g src p' v Hvalid_p') as [[Heq_nil _] | [p_pre [u [e_last [Heq_p [Hvalid_pre Hstep_last]]]]]].
      { subst. congruence. } 

      subst p'.
      destruct p_pre.
      { (* p' 只有一条边 src->v，矛盾 *)
        apply valid_epath_nil_inv in Hvalid_pre. subst u. 
        apply Hno_step. exists e_last. auto.
      }
      { (* p' 有多条边，倒数第二个点 u 必须是 src，矛盾 *)
        specialize (Hthru_p' (e :: p_pre) (e_last :: nil) u).
        assert (e :: p_pre <> nil) by discriminate.
        assert (e_last :: nil <> nil) by discriminate.
        specialize (Hthru_p' H H0 eq_refl Hvalid_pre).
        sets_unfold in Hthru_p'. subst u.
        apply Hno_step. exists e_last. auto.
      }
      
Qed.


(* TODO *)
Lemma init_satisfies_invariant:
  forall s : St, s = initSt -> loop_invariant s.
Proof.
  intros.
  unfold loop_invariant.
  repeat split; rewrite H.
  - unfold visited_dist_final.
    intros v0 Hv0.
    simpl in Hv0. sets_unfold in Hv0. subst v0.
    rewrite dist_initSt_src_zero.
    unfold min_value_weight_epath, min_value_of_subset_with_default.
    left. 
    split.
    + exists nil.
      split.
      * unfold min_object_of_subset. split.
        -- apply valid_epath_empty.
        -- intros p Hp.
           simpl.
           destruct (epath_weight g p) eqn:Hwp.
           ++ eapply valid_epath_non_neg; eauto. apply Hp.
           ++ simpl. trivial.
      * reflexivity.
    + simpl. trivial.
  - unfold unvisited_dist_optimal. intros.
    apply min_value_weight_epath_in_vset_empty.
  - unfold source_dist_zero; simpl.
    destruct (eq_dec src src); [reflexivity|].
    contradiction c; reflexivity.
  - unfold validity_constraint. unfold initSt; simpl. 
    intros. sets_unfold in H0. rewrite <- H0. exact valid_src.
  - intros v Hv.
    simpl in Hv. sets_unfold in Hv. subst v.
    unfold reachable.
    exists 0%nat. simpl. reflexivity.
    (* Locate clos_refl_trans. *)
  - intros v Hnot_reach.
    unfold initSt; simpl.
    destruct (eq_dec v src).
    (* Case 1: v = src *)
    + rewrite e in Hnot_reach. 
      assert (reachable src src). { unfold reachable; exists 0%nat. simpl. reflexivity. }
      tauto.
    (* Case 2: v <> src *)
    + set (Pred := fun (ow : option Z) => 
            (exists (e : E), step_aux g e src v /\ weight g e = ow) \/
            (ow = None /\ ~exists (e : E), step_aux g e src v)).
      
      assert (Hepsilon: Pred (Coq.Logic.ClassicalEpsilon.epsilon (inhabits None) Pred)).
      {
        (* 修复点：使用全名 Coq.Logic.ClassicalEpsilon.epsilon_spec *)
        apply Coq.Logic.ClassicalEpsilon.epsilon_spec.
        (* 证明存在一个值满足 Pred (这个值就是 None) *)
        exists None. right. split; [reflexivity |].
        (* 证明不存在边：如果有边，则 v 可达，矛盾 *)
        intros [e Hstep].
        apply Hnot_reach.
        apply step_rt. (* step_rt: step -> reachable *)
        exists e. exact Hstep.
      }
      destruct Hepsilon as [[e [Hstep _]] | [Hnone _]].
      * (* 情况 A: 假如判定存在边，导出矛盾 *)
        exfalso. apply Hnot_reach.
        apply step_rt. exists e. exact Hstep.
      * (* 情况 B: 判定不存在边，返回 None。正是我们要证的 *)
        exact Hnone.
Qed.



(* ✅ *)
Lemma init_ready : ready initSt.
Proof.
  destruct (init_satisfies_invariant initSt eq_refl) as [Hf [_ [Hz [Hv Hr]]]].
  split; [constructor|].
  - exact Hf.
  - intros x w Hd. destruct (min_value_weight_epath_in_vset_empty x)
      as [[[p [[Hp _] Hw]] _]|[_ Hnone]]; [exists p; split; [exact Hp|congruence]|congruence].
  - exact Hz.
  - reflexivity.
  - exact Hv.
  - exact Hr.
  - intros x e y Hx He. change (src = x) in Hx. subst.
    unfold edge_bound. rewrite dist_initSt_src_zero, Z_op_plus_O_l, <- single_weight.
    eapply minimum_lower; [apply min_value_weight_epath_in_vset_empty|].
    apply is_epath_through_vset_single. exact He.
Qed.

Theorem Dijkstra_final_state:
  Hoare (fun s => s = initSt)
        Dijkstra
        (fun _ s => ready s /\ unvisited_no_reachable s).
Proof.
  unfold Dijkstra.
  apply Hoare_conseq_pre with (P2:= fun s => ready s).
  1:{ intros s ->. apply init_ready. } (* init_satisfies_invariant: initSt 满足 loop_invariant *)
  apply Hoare_repeat_break' with (P:= fun _ s => ready s); intros.
  - apply continue_holds_invariant.
  - apply termination_implies_correctness.
Qed.

Theorem Dijkstra_correct:
  Hoare (fun s => s = initSt) Dijkstra (fun _ s => distance_correct s).
Proof.
  eapply Hoare_conseq_post; [|apply Dijkstra_final_state].
  intros _ s [Hready Hexit]. apply distance_correct_aux; auto using ready_invariant.
Qed.

(* 第三档难度：在上面的基础上证明，
      如果 e 是 v 到 u 的一条边，
      并且 d(s, u) = d(s, v) + length(e)，
      那么存在一条 s 到 u 的最短路径，其最后一条边是 e。*)
Theorem Dijkstra_prop_level3 (s : St) (u v : V) (e : E):
  distance_correct s ->       (* 假设 s 满足正确性（由 Dijkstra_correct 保证） *)
  unvisited_no_reachable s -> (* 终止状态 *)
  step_aux g e v u ->         (* e是从v到u的一条边 *)
  (exists dv, dist s v = Some dv) -> (* v 是可达的 *)
  dist s u = Z_op_plus (dist s v) (weight g e) ->
  exists p, valid_epath g src p u /\
            min_value_weight_epath g src u (epath_weight g p) /\
            exists p', p = p' ++ e :: nil.
Proof.
  intros H_correct H_term H_step [dv H_dv] H_dist_eq.
  
  (* 1. 利用正确性 (distance_correct)，从 v 的距离提取出最短路径 p' *)
  destruct H_correct as [H_sound H_complete].
  (* dist s v = Some dv，根据 soundness，说明这是真实的最短距离 *)
  assert (H_min_v: min_value_weight_epath g src v (Some dv)).
  { unfold distance_soundness in H_sound. apply H_sound. 
    - eapply step_vvalid1.
      apply H_step.
    - exact H_dv. }
  unfold min_value_weight_epath, min_value_of_subset_with_default in H_min_v.
  destruct H_min_v as [[H_ex_min _] | [_ H_none]].
  - (* Case 1: The min value exists and corresponds to a path (Left branch of min_value definition) *)
    destruct H_ex_min as [p_v [H_obj_pv H_weight_pv]].
    destruct H_obj_pv as [H_valid_pv H_opt_pv].
    
    (* Construct the new path by appending edge e *)
    exists (p_v ++ e :: nil).
    split.
    + eapply valid_epath_snoc; eauto. exact H_valid_pv.
    + split.
      * (* Subgoal 2: The weight of the new path corresponds to the min value *)
        (* First, expand the weight of the concatenated path *)
        rewrite epath_weight_app_assoc.
        rewrite H_weight_pv.
        
        (* Simplify the weight of the single edge list [e] *)
        unfold epath_weight. simpl.
        rewrite Z_op_plus_zero_r.
        change (match weight g e with
                | Some y => Some (dv + y)
                | None => None
                end) 
          with (Z_op_plus (Some dv) (weight g e)).
        rewrite <- H_dv.
        rewrite <- H_dist_eq.
        apply H_sound.
        -- (* 证明 u 是有效节点 *)
           eapply step_vvalid2; eauto.
        -- (* 证明相等性，已经是显然的了 *)
           reflexivity.
        
      * (* Subgoal 3: Structural requirement *)
        exists p_v. reflexivity.
  - (* Case 2: The set implies the default value None (Right branch) *)
    (* But we know dist s v = Some dv, so it cannot be None *)
    discriminate H_none.
Qed.

(** 第四档难度 *)
Record St_path := mkSt_path {
  visited_p : V -> Prop;
  path_p    : list E
}.

Definition initSt_path : St_path :=
{|
  visited_p := ∅;
  path_p := (@nil E)
|}.

Lemma reachable_vvalid:
  forall v, reachable src v -> vvalid g v.
Proof. 
  intros v H.
  unfold reachable in H.
  induction_n1 H.
  - apply valid_src.
  - pose proof (step_vvalid _ _ H0) as [_ H_valid_v].
    assumption.
Qed.

Lemma reachable_final_visited (s : St): 
  unvisited_no_reachable s -> (forall v, reachable src v -> visited s v).
Proof.
  intros.
  destruct (classic (visited s v)) as [H_vis | H_not_vis].
  - assumption.
  - exfalso.
    unfold unvisited_no_reachable, unvisited in H.
    pose proof (reachable_vvalid v H0).
    destruct (H v); tauto.
Qed.

Lemma epath_weight_nil:
  epath_weight g nil = Some 0.
Proof. unfold epath_weight. simpl. reflexivity. Qed.

Definition Dijkstra_construct_f (s0 : St) (u : V) : program St_path (CntOrBrk V unit) :=
  choice
    (assume (fun _ => u = src);; break tt) (* 到达源点，停止 *)
    ( assume (fun _ => ~(u = src));;
      v <- any V;; e <- any E;; (* 否则，沿最短路等式倒推 *)
      assume (fun _ => step_aux g e v u);;
      assume (fun _ => dist s0 u = Z_op_plus (dist s0 v) (weight g e));;
      assume (fun s => ~ v ∈ s.(visited_p));;
      update' (fun s => s 
        <| visited_p ::= fun vs => vs ∪ [v] |>
        <| path_p    ::= fun p  => e :: p |>);;
      continue v).

Definition Dijkstra_construct (s0 : St) (dest : V) : program St_path unit :=
  repeat_break (Dijkstra_construct_f s0) dest.

Lemma not_ex_ex_all_all_not : forall {A B : Type} (P : A -> B -> Prop),
  ~(exists a b, P a b) <-> (forall a b, ~P a b).
Proof.
  intros A B P1.
  split; intros H.
  - intros a b HPab.
    apply H.
    exists a, b.
    exact HPab.
  - intros [a [b HPab]].
    apply (H a b).
    exact HPab.
Qed.

Lemma dist_None_irreachable (s : St) (u : V): 
  distance_correct s ->
  unvisited_no_reachable s ->
  loop_invariant s ->
  dist s u = None ->
  ~reachable src u.
Proof.
  intros [Hsound _] _ _ Hd Hr.
  apply (proj2 (no_reachable_iff_min_value_weight_epath_None u)); [|exact Hr].
  apply Hsound; [apply reachable_vvalid; exact Hr|exact Hd].
Qed.

(* 非负整数权保证非空的路径权重集合有最小元，即使图无限。 *)
Lemma reachable_has_weight_minimal_path dest :
  reachable src dest -> exists p, valid_epath g src p dest /\
    min_value_weight_epath g src dest (epath_weight g p).
Proof.
  intros Hr. destruct (reachable_valid_epath g src dest Hr) as [p Hp].
  set (size := fun q : list E => Z.to_nat (match epath_weight g q with
                                           | Some w => w | None => 0 end)).
  induction p as [p IH] using (well_founded_induction (well_founded_ltof _ size)).
  destruct (classic (forall q, valid_epath g src q dest ->
              Z_op_le (epath_weight g p) (epath_weight g q))) as [Hmin|Hbetter].
  - exists p. split; [exact Hp|]. left. split; [|apply Z_op_le_none_r].
    exists p. split; [split; assumption|reflexivity].
  - apply not_all_ex_not in Hbetter as [q Hbetter].
    apply imply_to_and in Hbetter as [Hq Hlt]. apply (IH q); [|exact Hq].
    unfold ltof, size. pose proof (valid_epath_not_none _ _ _ Hp) as Hpn.
    pose proof (valid_epath_not_none _ _ _ Hq) as Hqn.
    destruct (epath_weight g p) as [wp|] eqn:Hwp; [|contradiction].
    destruct (epath_weight g q) as [wq|] eqn:Hwq; [|contradiction].
    pose proof (valid_epath_non_neg _ _ _ _ Hq Hwq). simpl in Hlt. lia.
Qed.

Definition cinv (s0 : St) (dest : V) (u : V) (sp : St_path) : Prop :=
  valid_epath g u (path_p sp) dest /\
  Z_op_plus (dist s0 u) (epath_weight g (path_p sp)) = dist s0 dest.

Definition cinv_continue (s0 : St) (dest : V) (v : (CntOrBrk V unit)) (sp : St_path) : Prop :=
  match v with
  | by_continue v => cinv s0 dest v sp
  | by_break _ => True
  end.

Definition cinv_break (s0 : St) (dest : V) (u : (CntOrBrk V unit)) (sp : St_path) : Prop :=
  match u with
  | by_continue _ => True
  | by_break _ => cinv s0 dest src sp
  end.

Lemma zero_loop (s : St) (dest : V) (p : list E) (sp : St_path):
  distance_correct s ->
  unvisited_no_reachable s ->
  loop_invariant s ->
  reachable src dest ->
  valid_epath g src (path_p sp) dest ->
  valid_epath g src (p ++ path_p sp) dest ->
  epath_weight g (p ++ path_p sp) = dist s dest ->
  epath_weight g p = Some 0.
Proof.
  intros [Hsound _] _ _ Hr Hsuffix Hwhole Hweight.
  pose proof (Hsound dest _ (reachable_vvalid dest Hr) eq_refl) as Hmin.
  pose proof (minimum_lower _ _ Hmin _ Hsuffix) as Hbound.
  destruct (valid_epath_app_inv g src p (path_p sp) dest Hwhole) as [u [Hp _]].
  rewrite <- Hweight, epath_weight_app_assoc in Hbound.
  pose proof (valid_epath_not_none _ _ _ Hp) as Hfinite.
  pose proof (valid_epath_not_none _ _ _ Hsuffix) as Hsuffix_finite.
  destruct (epath_weight g p) as [w|] eqn:Hw; [|contradiction].
  destruct (epath_weight g (path_p sp)); [|contradiction].
  pose proof (valid_epath_non_neg _ _ _ _ Hp Hw). simpl in Hbound. f_equal. lia.
Qed.

(* 没有终止性保证 *)
Theorem Dijkstra_construct_correct (s0 : St) (dest : V) :
  distance_correct s0 ->
  unvisited_no_reachable s0 ->
  loop_invariant s0 -> 
  reachable src dest ->
  Hoare 
    (fun sp => sp = initSt_path)
    (Dijkstra_construct s0 dest)
    (fun _ sp => valid_epath g src (path_p sp) dest /\
                  epath_weight g (path_p sp) = dist s0 dest).
Proof.
  intros _ _ [_ [_ [Hzero _]]] _.
  unfold Dijkstra_construct.
  eapply Hoare_conseq_pre; [|apply Hoare_repeat_break' with (P := cinv s0 dest)].
  - intros sp ->. split; [apply valid_epath_empty|]. simpl. apply Z_op_plus_O_r.
  - intro u. apply Hoare_bind with (Q := cinv_continue s0 dest).
    + unfold Dijkstra_construct_f. apply Hoare_choice.
      * apply Hoare_assume_bind. apply Hoare_ret'. simpl. tauto.
      * intro_state. hoare_auto.
        intro_state. destruct H0 as [? [? [? [? ?]]]].
        subst s2. rename a into v. rename a0 into e.
        eapply Hoare_bind.
        2:{ intros. apply Hoare_ret'. intros. simpl. exact H4. }
        eapply Hoare_conseq_post; [|apply Hoare_update].
        intros b last [before [Hupd ->]]. subst last.
        destruct H as [Hp Hsum].
        change (valid_epath g v (e :: path_p s1) dest /\
          Z_op_plus (dist s0 v) (epath_weight g (e :: path_p s1)) = dist s0 dest).
        split; [eapply valid_epath_cons; eauto|].
        change (Z_op_plus (dist s0 v) (Z_op_plus (weight g e) (epath_weight g (path_p s1))) = dist s0 dest).
        rewrite <- Hsum, H1. destruct (dist s0 v), (weight g e), (epath_weight g (path_p s1));
          simpl; try reflexivity; f_equal; lia.
    + intros [v|b]; [apply Hoare_ret'; auto|apply Hoare_empty].
  - intro u. apply Hoare_bind with (Q := cinv_break s0 dest).
    + unfold Dijkstra_construct_f. apply Hoare_choice.
      * apply Hoare_assume_bind. apply Hoare_ret'. intros sp [-> Hinv]. exact Hinv.
      * hoare_auto. apply Hoare_bind with (Q := fun _ _ => True).
        -- intros ? ? ? _ _. exact I.
        -- intros []. apply Hoare_ret'. simpl; auto.
    + intros [v|b]; [apply Hoare_empty|]. apply Hoare_ret'.
      intros sp [Hp Hsum]. split; [exact Hp|]. rewrite Hzero, Z_op_plus_O_l in Hsum. exact Hsum.
Qed.

Corollary Dijkstra_distance_and_path_correct s dest :
  (initSt, tt, s) ∈ Dijkstra -> reachable src dest ->
  distance_correct s /\
  Hoare (fun sp => sp = initSt_path) (Dijkstra_construct s dest)
    (fun _ sp => valid_epath g src (path_p sp) dest /\
                 epath_weight g (path_p sp) = dist s dest).
Proof.
  intros Hrun Hr.
  destruct (Dijkstra_final_state initSt tt s eq_refl Hrun) as [Hready Hexit].
  pose proof (ready_invariant s Hready) as Hinv.
  pose proof (distance_correct_aux s Hexit Hinv) as Hd.
  split; [exact Hd|apply Dijkstra_construct_correct; assumption].
Qed.

End Dijkstra.
