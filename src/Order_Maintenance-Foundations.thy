section \<open>Foundations\<close>

theory "Order_Maintenance-Foundations"
  imports Main
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

fun parent :: "vertex \<Rightarrow> vertex" where
  "parent \<langle>h, i\<rangle> = \<langle>Suc h, i div 2\<rangle>"

lemma parent_graph_is_acyclic:
  assumes "(parent ^^ n) v = v"
  shows "n = 0"
proof -
  from assms obtain h and i where "\<langle>h, i\<rangle> = (parent ^^ n) \<langle>h, i\<rangle>"
    by (metis vertex.collapse)
  also obtain i' where "\<dots> = \<langle>h + n, i'\<rangle>"
    by (induction n) simp_all
  finally show ?thesis
    by simp
qed

function (domintros)
  lowest_common_ancestor :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex" (infixl "\<squnion>" 65)
where
  "\<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle> = parent \<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle>" if "h\<^sub>1 < h\<^sub>2" |
  "\<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> \<langle>h\<^sub>2, i\<^sub>2\<rangle> = \<langle>h\<^sub>1, i\<^sub>1\<rangle> \<squnion> parent \<langle>h\<^sub>2, i\<^sub>2\<rangle>" if "h\<^sub>1 > h\<^sub>2" |
  "\<langle>h, i\<^sub>1\<rangle> \<squnion> \<langle>h, i\<^sub>2\<rangle> = parent \<langle>h, i\<^sub>1\<rangle> \<squnion> parent \<langle>h, i\<^sub>2\<rangle>" if "i\<^sub>1 \<noteq> i\<^sub>2" |
  "\<langle>h, i\<rangle> \<squnion> \<langle>h, i\<rangle> = \<langle>h, i\<rangle>"
  by (auto, metis vertex.exhaust not_less_iff_gr_or_eq)

lemma lowest_common_ancestor_is_total:
  shows "lowest_common_ancestor_dom (\<langle>h\<^sub>1, i\<^sub>1\<rangle>, \<langle>h\<^sub>2, i\<^sub>2\<rangle>)"
  sorry

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
