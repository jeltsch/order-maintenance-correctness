section \<open>Foundations\<close>

theory "Order_Maintenance-Foundations"
  imports Main
begin

subsection \<open>Element Labelings\<close>

typedef 'e element_labeling = "{m :: 'e \<rightharpoonup> nat. finite (dom m) \<and> inj_on m (dom m)}"
  by (rule exI [where x = Map.empty]) simp

definition elements :: "'e element_labeling \<Rightarrow> 'e set" where
  [simp]: "elements \<E> = dom (Rep_element_labeling \<E>)"

definition labels :: "'e element_labeling \<Rightarrow> nat set" where
  [simp]: "labels \<E> = ran (Rep_element_labeling \<E>)"

definition label_of :: "'e element_labeling \<Rightarrow> 'e \<Rightarrow> nat" where
  [simp]: "label_of \<E> e = the ((Rep_element_labeling \<E>) e)"

definition element_of :: "'e element_labeling \<Rightarrow> nat \<Rightarrow> 'e" where
  [simp]: "element_of \<E> l = (THE e. e \<in> elements \<E> \<and> label_of \<E> e = l)"

lemma element_of_after_label_of:
  assumes "e \<in> elements \<E>"
  shows "element_of \<E> (label_of \<E> e) = e"
  sorry

lemma label_of_after_element_of:
  assumes "l \<in> labels \<E>"
  shows "label_of \<E> (element_of \<E> l) = l"
  using assms
  sorry

subsection \<open>Supertrees\<close>

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: "index n h = n div 2 ^ h"

fun parent :: "nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "parent (h, i) = (Suc h, i div 2)"

lemma parent_graph_is_acyclic:
  assumes "parent ^^ n = id"
  shows "n = 0"
proof -
  have "\<exists>i'. (parent ^^ n) (h, i) = (h + n, i')" for h and i
    by (induction n) auto
  with assms show ?thesis
    by simp
qed

function (domintros)
  lowest_common_ancestor :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" (infixl "\<squnion>" 65)
where
  "h\<^sub>1 < h\<^sub>2 \<Longrightarrow> (h\<^sub>1, i\<^sub>1) \<squnion> (h\<^sub>2, i\<^sub>2) = (h\<^sub>2, i\<^sub>2 div 2 ^ (h\<^sub>2 - h\<^sub>1)) \<squnion> (h\<^sub>2, i\<^sub>2)" |
  "h\<^sub>1 > h\<^sub>2 \<Longrightarrow> (h\<^sub>1, i\<^sub>1) \<squnion> (h\<^sub>2, i\<^sub>2) = (h\<^sub>1, i\<^sub>1) \<squnion> (h\<^sub>1, i\<^sub>1 div 2 ^ (h\<^sub>1 - h\<^sub>2))" |
  "i\<^sub>1 \<noteq> i\<^sub>2 \<Longrightarrow> (h, i\<^sub>1) \<squnion> (h, i\<^sub>2) = (Suc h, i\<^sub>1 div 2) \<squnion> (Suc h, i\<^sub>2 div 2)" |
  "(h, i) \<squnion> (h, i) = (h, i)"
  by fastforce+

lemma lowest_common_ancestor_is_total:
  shows "lowest_common_ancestor_dom ((h\<^sub>1, i\<^sub>1), (h\<^sub>2, i\<^sub>2))"
  sorry

fun labels_under :: "nat \<times> nat \<Rightarrow> nat set" where
  "labels_under (h, i) = {2 ^ h * i .. 2 ^ h * i + 2 ^ h - 1}"

lemma labels_under_is_finite:
  shows "finite (labels_under (h, i))"
  by simp

lemma labels_under_cardinality:
  shows "card (labels_under (h, i)) = 2 ^ h"
  by simp

end
