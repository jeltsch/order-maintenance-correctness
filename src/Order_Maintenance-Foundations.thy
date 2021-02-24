section \<open>Foundations\<close>

theory "Order_Maintenance-Foundations"
  imports Main "HOL-Library.Lattice_Syntax"
begin

subsection \<open>Element Labelings\<close>

typedef 'e element_labeling = "{m :: 'e \<rightharpoonup> nat. finite (dom m) \<and> inj_on m (dom m)}"
  by (rule exI [where x = Map.empty]) simp

setup_lifting type_definition_element_labeling

lift_definition elements :: "'e element_labeling \<Rightarrow> 'e set"
  is dom .

lift_definition labels :: "'e element_labeling \<Rightarrow> nat set"
  is ran .

lift_definition label_of :: "'e element_labeling \<Rightarrow> 'e \<Rightarrow> nat"
  is "\<lambda>m e. the (m e)" .

definition element_of :: "'e element_labeling \<Rightarrow> nat \<Rightarrow> 'e" where
  [simp]: "element_of \<E> l = (THE e. e \<in> elements \<E> \<and> label_of \<E> e = l)"

lemma element_of_after_label_of:
  assumes "e \<in> elements \<E>"
  shows "element_of \<E> (label_of \<E> e) = e"
  unfolding element_of_def
  using assms
  by transfer (rule the_equality, simp, metis domIff option.expand inj_onD)

lemma label_of_after_element_of:
  assumes "l \<in> labels \<E>"
  shows "label_of \<E> (element_of \<E> l) = l"
  unfolding element_of_def
  using assms
  by transfer (smt inj_onD dom_def ran_def not_None_eq mem_Collect_eq option.sel theI')

subsection \<open>Supertrees\<close>

datatype vertex = Vertex (height: \<open>nat\<close>) (index: \<open>nat\<close>) (\<open>\<langle>_, _\<rangle>\<close>)

definition leaves :: "vertex set" where
  [simp]: "leaves = {v. height v = 0}"

fun parent :: "vertex \<Rightarrow> vertex" where
  "parent \<langle>h, i\<rangle> = \<langle>Suc h, i div 2\<rangle>"

definition is_child_of :: "vertex \<Rightarrow> vertex \<Rightarrow> bool" where
  [iff]: "is_child_of v v' \<longleftrightarrow> v' = parent v"

lemma descendant_is_lower:
  assumes "is_child_of\<^sup>+\<^sup>+ v v'"
  shows "height v < height v'"
  using assms
  by induction (metis vertex.collapse vertex.sel(1) is_child_of_def parent.simps less_Suc_eq)+

lemma descendant_or_self_is_at_most_as_high:
  assumes "is_child_of\<^sup>*\<^sup>* v v'"
  shows "height v \<le> height v'"
  using descendant_is_lower and assms
  by (auto simp add: Nitpick.rtranclp_unfold intro: less_imp_le_nat)

lemma is_child_of_is_acyclic:
  shows "irreflp is_child_of\<^sup>+\<^sup>+"
  by (rule irreflpI, rule notI) (blast dest: descendant_is_lower)

instantiation vertex :: semilattice_sup
begin

definition less_eq_vertex :: "vertex \<Rightarrow> vertex \<Rightarrow> bool" where
  [iff]: "(\<le>) = is_child_of\<^sup>*\<^sup>*"

definition less_vertex :: "vertex \<Rightarrow> vertex \<Rightarrow> bool" where
  [iff]: "(<) = is_child_of\<^sup>+\<^sup>+"

function sup_vertex :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex" where
  ascending_simp:
    "\<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle> = parent \<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle>" if "h\<^sub>1 < h\<^sub>2" |
  descending_simp:
    "\<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle> = \<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> parent \<langle>h\<^sub>2, i\<^sub>2\<rangle>" if "h\<^sub>1 > h\<^sub>2" |
  different_indices_simp:
    "\<langle>h, i\<^sub>1\<rangle> \<squnion> \<langle>h, i\<^sub>2\<rangle> = parent \<langle>h, i\<^sub>1\<rangle> \<squnion> parent \<langle>h, i\<^sub>2\<rangle>" if "i\<^sub>1 \<noteq> i\<^sub>2" |
  equal_vertices_simp:
    "\<langle>h, i\<rangle> \<squnion> \<langle>h, i\<rangle> = \<langle>h, i\<rangle>"
  by (auto, metis vertex.exhaust not_less_iff_gr_or_eq)
  termination sorry

lemmas sup_vertex_induct [case_names ascending descending different_indices equal_vertices] =
  sup_vertex.induct

instance proof
  show "v < v' \<longleftrightarrow> v \<le> v' \<and> \<not> v' \<le> v" for v v' :: vertex
  unfolding less_vertex_def and less_eq_vertex_def proof
    assume "is_child_of\<^sup>+\<^sup>+ v v'"
    show "is_child_of\<^sup>*\<^sup>* v v' \<and> \<not> is_child_of\<^sup>*\<^sup>* v' v"
    proof
      from \<open>is_child_of\<^sup>+\<^sup>+ v v'\<close> show "is_child_of\<^sup>*\<^sup>* v v'"
        by (fact tranclp_into_rtranclp)
    next
      from \<open>is_child_of\<^sup>+\<^sup>+ v v'\<close> show "\<not> is_child_of\<^sup>*\<^sup>* v' v"
        using is_child_of_is_acyclic
        unfolding irreflp_def
        by (blast intro: tranclp_rtranclp_tranclp)
    qed
  next
    assume "is_child_of\<^sup>*\<^sup>* v v' \<and> \<not> is_child_of\<^sup>*\<^sup>* v' v"
    then show "is_child_of\<^sup>+\<^sup>+ v v'"
      by (blast dest: rtranclpD)
  qed
next
  show "v \<le> v" for v :: vertex
    by simp
next
  show "v \<le> v''" if "v \<le> v'" and "v' \<le> v''" for v v' v'' :: vertex
    using that
    by simp
next
  show "v\<^sub>1 = v\<^sub>2" if "v\<^sub>1 \<le> v\<^sub>2" and "v\<^sub>2 \<le> v\<^sub>1" for v\<^sub>1 v\<^sub>2 :: vertex
    using is_child_of_is_acyclic and that
    unfolding irreflp_def and less_eq_vertex_def
    by (blast dest: rtranclpD intro: tranclp_rtranclp_tranclp)
next
  show "v\<^sub>1 \<le> v\<^sub>1 \<squnion> v\<^sub>2" for v\<^sub>1 v\<^sub>2 :: vertex
  unfolding less_eq_vertex_def proof (induction v\<^sub>1 v\<^sub>2 rule: sup_vertex_induct)
    case ascending
    then show ?case
      by (auto intro: converse_rtranclp_into_rtranclp simp only: ascending_simp)
  next
    case descending
    then show ?case
      by (simp only: descending_simp)
  next
    case different_indices
    then show ?case
      by (metis is_child_of_def converse_rtranclp_into_rtranclp different_indices_simp)
  next
    case equal_vertices
    then show ?case
      by (simp only: equal_vertices_simp)
  qed
next
  show "v\<^sub>2 \<le> v\<^sub>1 \<squnion> v\<^sub>2" for v\<^sub>1 v\<^sub>2 :: vertex
  unfolding less_eq_vertex_def proof (induction v\<^sub>1 v\<^sub>2 rule: sup_vertex_induct)
    case ascending
    then show ?case
      by (simp only: ascending_simp)
  next
    case descending
    then show ?case
      by (auto intro: converse_rtranclp_into_rtranclp simp only: descending_simp)
  next
    case different_indices
    then show ?case
      by (metis is_child_of_def converse_rtranclp_into_rtranclp different_indices_simp)
  next
    case equal_vertices
    then show ?case
      by (simp only: equal_vertices_simp)
  qed
next
  show "v\<^sub>1 \<squnion> v\<^sub>2 \<le> v'" if "v\<^sub>1 \<le> v'" and "v\<^sub>2 \<le> v'" for v\<^sub>1 v\<^sub>2 v' :: vertex
  using that unfolding less_eq_vertex_def proof (induction v\<^sub>1 v\<^sub>2 rule: sup_vertex_induct)
    case (ascending h\<^sub>1 h\<^sub>2 i\<^sub>1 i\<^sub>2)
    from \<open>is_child_of\<^sup>*\<^sup>* \<langle>h\<^sub>2, i\<^sub>2\<rangle> v'\<close> have "h\<^sub>2 \<le> height v'"
      by (auto dest: descendant_or_self_is_at_most_as_high)
    with \<open>h\<^sub>1 < h\<^sub>2\<close> have "h\<^sub>1 \<noteq> height v'"
      by simp
    with \<open>is_child_of\<^sup>*\<^sup>* \<langle>h\<^sub>1, i\<^sub>1\<rangle> v'\<close> have "is_child_of\<^sup>+\<^sup>+ \<langle>h\<^sub>1, i\<^sub>1\<rangle> v'"
      by (auto dest: rtranclpD)
    then have "is_child_of\<^sup>*\<^sup>* (parent \<langle>h\<^sub>1, i\<^sub>1\<rangle>) v'"
      by (blast dest: tranclpD)
    with ascending.IH and \<open>is_child_of\<^sup>*\<^sup>* (\<langle>h\<^sub>2, i\<^sub>2\<rangle>) v'\<close>
    have "is_child_of\<^sup>*\<^sup>* (parent \<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle>) v'"
      by blast
    with \<open>h\<^sub>1 < h\<^sub>2\<close> show ?case
      by (simp only: ascending_simp)
  next
    case (descending h\<^sub>1 h\<^sub>2 i\<^sub>1 i\<^sub>2)
    from \<open>is_child_of\<^sup>*\<^sup>* \<langle>h\<^sub>1, i\<^sub>1\<rangle> v'\<close> have "h\<^sub>1 \<le> height v'"
      by (auto dest: descendant_or_self_is_at_most_as_high)
    with \<open>h\<^sub>1 > h\<^sub>2\<close> have "h\<^sub>2 \<noteq> height v'"
      by simp
    with \<open>is_child_of\<^sup>*\<^sup>* \<langle>h\<^sub>2, i\<^sub>2\<rangle> v'\<close> have "is_child_of\<^sup>+\<^sup>+ \<langle>h\<^sub>2, i\<^sub>2\<rangle> v'"
      by (auto dest: rtranclpD)
    then have "is_child_of\<^sup>*\<^sup>* (parent \<langle>h\<^sub>2, i\<^sub>2\<rangle>) v'"
      by (blast dest: tranclpD)
    with descending.IH and \<open>is_child_of\<^sup>*\<^sup>* (\<langle>h\<^sub>1, i\<^sub>1\<rangle>) v'\<close>
    have "is_child_of\<^sup>*\<^sup>* (\<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> parent \<langle>h\<^sub>2, i\<^sub>2\<rangle>) v'"
      by blast
    with \<open>h\<^sub>1 > h\<^sub>2\<close> show ?case
      by (simp only: descending_simp)
  next
    case (different_indices i\<^sub>1 i\<^sub>2 h)
    from \<open>is_child_of\<^sup>*\<^sup>* \<langle>h, i\<^sub>1\<rangle> v'\<close> and \<open>is_child_of\<^sup>*\<^sup>* \<langle>h, i\<^sub>2\<rangle> v'\<close>
    consider
      (as_high_as_sup)
        "\<langle>h, i\<^sub>1\<rangle> = v'" and "\<langle>h, i\<^sub>2\<rangle> = v'" |
      (lower_than_sup)
        "is_child_of\<^sup>+\<^sup>+ \<langle>h, i\<^sub>1\<rangle> v'" and "is_child_of\<^sup>+\<^sup>+ \<langle>h, i\<^sub>2\<rangle> v'"
      by (fastforce dest: rtranclpD descendant_is_lower)
    then show ?case
    proof cases
      case as_high_as_sup
      from \<open>\<langle>h, i\<^sub>1\<rangle> = v'\<close> and \<open>\<langle>h, i\<^sub>2\<rangle> = v'\<close> have "i\<^sub>1 = i\<^sub>2"
        by blast
      with \<open>i\<^sub>1 \<noteq> i\<^sub>2\<close> show ?thesis
        by simp
    next
      case lower_than_sup
      from \<open>is_child_of\<^sup>+\<^sup>+ \<langle>h, i\<^sub>1\<rangle> v'\<close> have "is_child_of\<^sup>*\<^sup>* (parent \<langle>h, i\<^sub>1\<rangle>) v'"
        by (blast dest: tranclpD)
      moreover
      from \<open>is_child_of\<^sup>+\<^sup>+ \<langle>h, i\<^sub>2\<rangle> v'\<close> have "is_child_of\<^sup>*\<^sup>* (parent \<langle>h, i\<^sub>2\<rangle>) v'"
        by (blast dest: tranclpD)
      ultimately have "is_child_of\<^sup>*\<^sup>* (parent \<langle>h, i\<^sub>1\<rangle> \<squnion> parent \<langle>h, i\<^sub>2\<rangle>) v'"
        using different_indices.IH
        by blast
      then show ?thesis
        unfolding different_indices_simp [OF \<open>i\<^sub>1 \<noteq> i\<^sub>2\<close>] .
    qed
  next
    case equal_vertices
    then show ?case
      by (simp only: equal_vertices_simp)
  qed
qed

end

definition index_at_height :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: "index_at_height l h = l div 2 ^ h"

fun labels_under :: "vertex \<Rightarrow> nat set" where
  "labels_under \<langle>h, i\<rangle> = {2 ^ h * i .. 2 ^ h * i + 2 ^ h - 1}"

lemma labels_under_is_finite:
  shows "finite (labels_under \<langle>h, i\<rangle>)"
  by simp

lemma labels_under_cardinality:
  shows "card (labels_under \<langle>h, i\<rangle>) = 2 ^ h"
  by simp

end
