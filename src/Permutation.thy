theory Permutation
imports Main
begin

type_synonym 'a swp = "'a \<times> 'a"
type_synonym 'a preprm = "'a swp list"

definition preprm_id :: "'a preprm" where "preprm_id = []"

fun swp_apply :: "'a swp \<Rightarrow> 'a \<Rightarrow> 'a" where
  "swp_apply (a, b) x = (if x = a then b else (if x = b then a else x))"

fun preprm_apply :: "'a preprm \<Rightarrow> 'a \<Rightarrow> 'a" where
  "preprm_apply [] x = x"
| "preprm_apply (s # ss) x = swp_apply s (preprm_apply ss x)"

definition preprm_compose :: "'a preprm \<Rightarrow> 'a preprm \<Rightarrow> 'a preprm" where
  "preprm_compose f g \<equiv> f @ g"

definition preprm_unit :: "'a \<Rightarrow> 'a \<Rightarrow> 'a preprm" where
  "preprm_unit a b \<equiv> [(a, b)]"

definition preprm_ext :: "'a preprm \<Rightarrow> 'a preprm \<Rightarrow> bool" (infix "=p" 100) where
  "\<pi>\<^sub>1 =p \<pi>\<^sub>2 \<equiv> \<forall>x. preprm_apply \<pi>\<^sub>1 x = preprm_apply \<pi>\<^sub>2 x"

lemma swp_apply_unequal:
  assumes "x \<noteq> y"
  shows "swp_apply s x \<noteq> swp_apply s y"
proof(cases s)
  case (Pair a b)
    consider "x = a" | "x = b" | "x \<noteq> a \<and> x \<noteq> b" by auto
    thus ?thesis proof(cases)
      case 1
        have "swp_apply s x = b" using `s = (a, b)` `x = a` by simp
        moreover have "swp_apply s y \<noteq> b" using `s = (a, b)` `x = a` `x \<noteq> y`
          by(cases "y = b", simp_all)
        ultimately show ?thesis by metis
      next
      case 2
        have "swp_apply s x = a" using `s = (a, b)` `x = b` by simp
        moreover have "swp_apply s y \<noteq> a" using `s = (a, b)` `x = b` `x \<noteq> y`
          by(cases "y = a", simp_all)
        ultimately show ?thesis by metis
      next
      case 3
        have "swp_apply s x = x" using `s = (a, b)` `x \<noteq> a \<and> x \<noteq> b` by simp
        consider "y = a" | "y = b" | "y \<noteq> a \<and> y \<noteq> b" by auto
        hence "swp_apply s y \<noteq> x" proof(cases)
          case 1
            hence "swp_apply s y = b" using `s = (a, b)` by simp
            thus ?thesis using `x \<noteq> a \<and> x \<noteq> b` by metis
          next
          case 2
            hence "swp_apply s y = a" using `s = (a, b)` by simp
            thus ?thesis using `x \<noteq> a \<and> x \<noteq> b` by metis
          next
          case 3
            hence "swp_apply s y = y" using `s = (a, b)` by simp
            thus ?thesis using `x \<noteq> y` by metis
          next
        qed
        thus ?thesis using `swp_apply s x = x` `x \<noteq> y` by metis
      next
    qed
  next
qed

lemma swp_compose_push:
  shows
    "preprm_compose (preprm_unit a b) (preprm_unit c d) =p
     preprm_compose (preprm_unit c d) (preprm_unit
      (preprm_apply (preprm_unit c d) a)
      (preprm_apply (preprm_unit c d) b))"
unfolding preprm_unit_def preprm_compose_def preprm_ext_def proof
  fix x
  consider "x = a" | "x = b" | "x = c" | "x = d" | "x \<noteq> a \<and> x \<noteq> b \<and> x \<noteq> c \<and> x \<noteq> d" by auto
  thus
    "preprm_apply ([(a, b)] @ [(c, d)]) x =
     preprm_apply ([(c, d)] @ [(preprm_apply [(c, d)] a, preprm_apply [(c, d)] b)]) x"
   by(cases, simp_all)
qed

lemma preprm_ext_reflexive:
  shows "x =p x"
unfolding preprm_ext_def by auto

corollary preprm_ext_reflp:
  shows "reflp preprm_ext"
unfolding reflp_def using preprm_ext_reflexive by auto

lemma preprm_ext_symmetric:
  assumes "x =p y"
  shows "y =p x"
using assms unfolding preprm_ext_def by auto

corollary preprm_ext_symp:
  shows "symp preprm_ext"
unfolding symp_def using preprm_ext_symmetric by auto

lemma preprm_ext_transitive:
  assumes "x =p y" and "y =p z"
  shows "x =p z"
using assms unfolding preprm_ext_def by auto

corollary preprm_ext_transp:
  shows "transp preprm_ext"
unfolding transp_def using preprm_ext_transitive by auto

lemma preprm_apply_composition:
  shows "preprm_apply (preprm_compose f g) x = preprm_apply f (preprm_apply g x)"
unfolding preprm_compose_def
by(induction f, simp_all)

lemma preprm_apply_unequal:
  assumes "x \<noteq> y"
  shows "preprm_apply \<pi> x \<noteq> preprm_apply \<pi> y"
using assms proof(induction \<pi>, simp)
  case (Cons s ss)
    have  "preprm_apply (s # ss) x = swp_apply s (preprm_apply ss x)"
      and "preprm_apply (s # ss) y = swp_apply s (preprm_apply ss y)" by auto
    thus ?case using Cons.IH `x \<noteq> y` swp_apply_unequal by metis
  next
qed

lemma preprm_unit_equal:
  shows "preprm_unit a a =p preprm_id"
unfolding preprm_ext_def preprm_unit_def preprm_id_def
by simp

lemma preprm_unit_inaction:
  assumes "x \<noteq> a" and "x \<noteq> b"
  shows "preprm_apply (preprm_unit a b) x = x"
unfolding preprm_unit_def using assms by simp

lemma preprm_unit_commutes:
  shows "preprm_unit a b =p preprm_unit b a"
unfolding preprm_ext_def preprm_unit_def
by simp

lemma preprm_unit_involution:
  shows "preprm_compose (preprm_unit a b) (preprm_unit a b) =p preprm_id"
unfolding preprm_ext_def preprm_compose_def preprm_unit_def preprm_id_def
by simp

lemma preprm_unit_transfers:
  fixes a b x y :: 'a
  assumes "x = preprm_apply (preprm_unit a b) y"
  shows "preprm_apply (preprm_unit a b) x = y"
using assms unfolding preprm_unit_def by simp

lemma preprm_apply_id:
  shows "preprm_apply preprm_id x = x"
unfolding preprm_id_def
by simp

lemma preprm_compose_associative:
  shows "preprm_compose (preprm_compose f g) h =p preprm_compose f (preprm_compose g h)"
unfolding preprm_ext_def preprm_compose_def
by simp

lemma preprm_compose_left_id:
  shows "preprm_compose preprm_id f =p f"
unfolding preprm_ext_def preprm_compose_def preprm_id_def
by simp

lemma preprm_compose_right_id:
  shows "preprm_compose f preprm_id =p f"
unfolding preprm_ext_def preprm_compose_def preprm_id_def
by simp

quotient_type 'a prm = "'a preprm" / preprm_ext
proof(rule equivpI)
  show "reflp preprm_ext" using preprm_ext_reflp.
  show "symp preprm_ext" using preprm_ext_symp.
  show "transp preprm_ext" using preprm_ext_transp.
qed

lift_definition prm_id :: "'a prm" ("\<epsilon>") is preprm_id.

lift_definition prm_apply :: "'a prm \<Rightarrow> 'a \<Rightarrow> 'a" (infix "$" 140) is preprm_apply
unfolding preprm_ext_def
using preprm_apply.simps by auto

lift_definition prm_compose :: "'a prm \<Rightarrow> 'a prm \<Rightarrow> 'a prm" (infixr "\<circ>" 145) is preprm_compose
unfolding preprm_ext_def
by(simp only: preprm_apply_composition, simp)

definition prm_apply_set :: "'a prm \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "{$}" 140) where
  "prm_apply_set \<pi> S \<equiv> image (prm_apply \<pi>) S"

lift_definition prm_unit :: "'a \<Rightarrow> 'a \<Rightarrow> 'a prm" ("[_ \<leftrightarrow> _]") is preprm_unit.

lemma prm_compose_push:
  shows "[a \<leftrightarrow> b] \<circ> [c \<leftrightarrow> d] = [c \<leftrightarrow> d] \<circ> [[c \<leftrightarrow> d] $ a \<leftrightarrow> [c \<leftrightarrow> d] $ b]"
by(transfer, metis swp_compose_push)

lemma prm_apply_composition:
  shows "f \<circ> g $ x = f $ (g $ x)"
by(transfer, metis preprm_apply_composition)

lemma prm_apply_unequal:
  assumes "x \<noteq> y"
  shows "\<pi> $ x \<noteq> \<pi> $ y"
using assms by(transfer, metis preprm_apply_unequal)

lemma prm_unit_equal_id:
  fixes a :: 'a
  shows "[a \<leftrightarrow> a] = \<epsilon>"
by(transfer, metis preprm_unit_equal)

lemma prm_unit_inaction:
  fixes a b x :: 'a
  assumes "x \<noteq> a" and "x \<noteq> b"
  shows "[a \<leftrightarrow> b] $ x = x"
using assms
by(transfer, metis preprm_unit_inaction)

lemma prm_unit_commutes:
  fixes a b :: 'a
  shows "[a \<leftrightarrow> b] = [b \<leftrightarrow> a]"
by (transfer, metis preprm_unit_commutes)

lemma prm_unit_involution:
  fixes a b :: 'a
  shows "[a \<leftrightarrow> b] \<circ> [a \<leftrightarrow> b] = \<epsilon>"
by(transfer, metis preprm_unit_involution)

lemma prm_unit_transfers:
  fixes a b x y :: 'a
  assumes "x = [a \<leftrightarrow> b] $ y"
  shows "[a \<leftrightarrow> b] $ x = y"
using assms by(transfer, metis preprm_unit_transfers)

lemma prm_apply_id:
  fixes x :: 'a
  shows "\<epsilon> $ x = x"
by(transfer, metis preprm_apply_id)

lemma prm_compose_associative:
  fixes f g h :: "'a prm"
  shows "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
by(transfer, metis preprm_compose_associative)

lemma prm_compose_left_id:
  fixes f :: "'a prm"
  shows "\<epsilon> \<circ> f = f"
by(transfer, metis preprm_compose_left_id)

lemma prm_compose_right_id:
  fixes f :: "'a prm"
  shows "f \<circ> \<epsilon> = f"
by(transfer, metis preprm_compose_right_id)



interpretation prm: semigroup prm_compose
unfolding semigroup_def
using prm_compose_associative
by auto

interpretation prm: monoid prm_compose prm_id
unfolding monoid_def monoid_axioms_def
using prm.semigroup_axioms prm_compose_left_id prm_compose_right_id
by auto
end