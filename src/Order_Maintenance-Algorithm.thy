section \<open>Algorithm\<close>

theory "Order_Maintenance-Algorithm"
  imports "Order_Maintenance-Data_Structure" "HOL.Real"
begin

locale algorithm_instance = element_supply +
  fixes threshold_base :: real (\<open>\<^bold>T\<close>)
  assumes "\<^bold>T \<in> {1 <..< 2}"
  (*FIXME: This is not yet the final story but the structure for the algorithm by Bender et al. *)

definition (in algorithm_instance)
  threshold_exceeded :: "'e element_labeling \<Rightarrow> vertex \<Rightarrow> bool"
where
  [simp]: "threshold_exceeded \<E> v \<longleftrightarrow> card (labels \<E> \<inter> labels_under v) > \<^bold>T ^ height v"

definition insert_element_with_label :: "'e \<Rightarrow> nat \<Rightarrow> 'e state \<Rightarrow> 'e state" where
  [simp]: "insert_element_with_label e l S = undefined"
  (*FIXME: Add the actual implementation. *)

fun new_element_with_label :: "nat \<Rightarrow> 'e state \<Rightarrow> 'e state" where
  "new_element_with_label l (\<E>, R) = insert_element_with_label (fresh_element \<E>) l (\<E>, R)"

end
