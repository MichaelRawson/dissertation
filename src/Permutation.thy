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
  "\<pi> =p \<sigma> \<equiv> \<forall>x. preprm_apply \<pi> x = preprm_apply \<sigma> x"

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

lemma preprm_unit_equal_id:
  shows "preprm_unit a a =p preprm_id"
unfolding preprm_ext_def preprm_unit_def preprm_id_def
by simp

lemma preprm_unit_inaction:
  assumes "x \<noteq> a" and "x \<noteq> b"
  shows "preprm_apply (preprm_unit a b) x = x"
unfolding preprm_unit_def using assms by simp

lemma preprm_unit_action:
  shows "preprm_apply (preprm_unit a b) a = b"
unfolding preprm_unit_def by simp

lemma preprm_unit_commutes:
  shows "preprm_unit a b =p preprm_unit b a"
unfolding preprm_ext_def preprm_unit_def
by simp

lemma preprm_unit_involution:
  shows "preprm_compose (preprm_unit a b) (preprm_unit a b) =p preprm_id"
unfolding preprm_ext_def preprm_compose_def preprm_unit_def preprm_id_def
by simp

lemma preprm_apply_id:
  shows "preprm_apply preprm_id x = x"
unfolding preprm_id_def
by simp

lemma preprm_apply_injective:
  shows "inj (preprm_apply \<pi>)"
unfolding inj_on_def proof(rule+)
  fix x y
  assume "preprm_apply \<pi> x = preprm_apply \<pi> y"
  thus "x = y" proof(induction \<pi>)
    case Nil
      thus ?case by auto
    next
    case (Cons s ss)
      hence "swp_apply s (preprm_apply ss x) = swp_apply s (preprm_apply ss y)" by auto
      thus ?case using swp_apply_unequal Cons.IH by metis
    next
  qed
qed

lemma preprm_disagreement_composition:
  assumes "a \<noteq> b" "b \<noteq> c" "a \<noteq> c"
  shows "{x.
    preprm_apply (preprm_compose (preprm_unit a b) (preprm_unit b c)) x \<noteq>
    preprm_apply (preprm_unit a c) x
  } = {a, b}"
unfolding preprm_unit_def preprm_compose_def proof
  show "{x. preprm_apply ([(a, b)] @ [(b, c)]) x \<noteq> preprm_apply [(a, c)] x} \<subseteq> {a, b}"
  proof
    fix x
    have "x \<notin> {a, b} \<Longrightarrow> x \<notin> {x. preprm_apply ([(a, b)] @ [(b, c)]) x \<noteq> preprm_apply [(a, c)] x}"
    proof -
      assume "x \<notin> {a, b}"
      hence "x \<noteq> a \<and> x \<noteq> b" by auto
      hence "preprm_apply ([(a, b)] @ [(b, c)]) x = preprm_apply [(a, c)] x" by simp
      thus "x \<notin> {x. preprm_apply ([(a, b)] @ [(b, c)]) x \<noteq> preprm_apply [(a, c)] x}" by auto
    qed
    thus "x \<in> {x. preprm_apply ([(a, b)] @ [(b, c)]) x \<noteq> preprm_apply [(a, c)] x} \<Longrightarrow> x \<in> {a, b}"
      by blast
  qed
  show "{a, b} \<subseteq> {x. preprm_apply ([(a, b)] @ [(b, c)]) x \<noteq> preprm_apply [(a, c)] x}"
  proof
    fix x
    assume "x \<in> {a, b}"
    from this consider "x = a" | "x = b" by auto
    thus "x \<in> {x. preprm_apply ([(a, b)] @ [(b, c)]) x \<noteq> preprm_apply [(a, c)] x}"
      using assms by(cases, simp_all)
  qed
qed

lemma preprm_compose_push:
  shows "
    preprm_compose \<pi> (preprm_unit a b) =p
    preprm_compose (preprm_unit (preprm_apply \<pi> a) (preprm_apply \<pi> b)) \<pi>
  "
unfolding preprm_ext_def preprm_unit_def
by (simp add: inj_eq preprm_apply_composition preprm_apply_injective)

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

lift_definition prm_compose :: "'a prm \<Rightarrow> 'a prm \<Rightarrow> 'a prm" (infixr "\<diamondop>" 145) is preprm_compose
unfolding preprm_ext_def
by(simp only: preprm_apply_composition, simp)

lift_definition prm_unit :: "'a \<Rightarrow> 'a \<Rightarrow> 'a prm" ("[_ \<leftrightarrow> _]") is preprm_unit.

lemma prm_apply_composition:
  fixes f g :: "'a prm" and x :: 'a
  shows "f \<diamondop> g $ x = f $ (g $ x)"
by(transfer, metis preprm_apply_composition)

lemma prm_apply_unequal:
  fixes \<pi> :: "'a prm" and x y :: 'a
  assumes "x \<noteq> y"
  shows "\<pi> $ x \<noteq> \<pi> $ y"
using assms by (transfer, metis preprm_apply_unequal)

lemma prm_unit_equal_id:
  fixes a :: 'a
  shows "[a \<leftrightarrow> a] = \<epsilon>"
by (transfer, metis preprm_unit_equal_id)

lemma prm_unit_inaction:
  fixes a b x :: 'a
  assumes "x \<noteq> a" and "x \<noteq> b"
  shows "[a \<leftrightarrow> b] $ x = x"
using assms
by (transfer, metis preprm_unit_inaction)

lemma prm_unit_action:
  fixes a b :: 'a
  shows "[a \<leftrightarrow> b] $ a = b"
by (transfer, metis preprm_unit_action)

lemma prm_unit_commutes:
  fixes a b :: 'a
  shows "[a \<leftrightarrow> b] = [b \<leftrightarrow> a]"
by (transfer, metis preprm_unit_commutes)

lemma prm_unit_involution:
  fixes a b :: 'a
  shows "[a \<leftrightarrow> b] \<diamondop> [a \<leftrightarrow> b] = \<epsilon>"
by (transfer, metis preprm_unit_involution)

lemma prm_apply_id:
  fixes x :: 'a
  shows "\<epsilon> $ x = x"
by(transfer, metis preprm_apply_id)

lemma prm_apply_injective:
  shows "inj (prm_apply \<pi>)"
by(transfer, metis preprm_apply_injective)

definition prm_set :: "'a prm \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "{$}" 140) where
  "prm_set \<pi> S \<equiv> image (prm_apply \<pi>) S"

lemma prm_set_membership:
  assumes "x \<in> S"
  shows "\<pi> $ x \<in> \<pi> {$} S"
using assms unfolding prm_set_def by simp

lemma prm_set_notmembership:
  assumes "x \<notin> S"
  shows "\<pi> $ x \<notin> \<pi> {$} S"
using assms unfolding prm_set_def 
by (simp add: inj_image_mem_iff prm_apply_injective)

lemma prm_set_singleton:
  shows "\<pi> {$} {x} = {\<pi> $ x}"
unfolding prm_set_def by auto

lemma prm_set_unit_inaction:
  assumes "a \<notin> S" and "b \<notin> S"
  shows "[a \<leftrightarrow> b] {$} S = S"
proof
  show "[a \<leftrightarrow> b] {$} S \<subseteq> S" proof
    fix x
    assume H: "x \<in> [a \<leftrightarrow> b] {$} S"
    from this obtain y where "x = [a \<leftrightarrow> b] $ y" unfolding prm_set_def using imageE by metis
    hence "y \<in> S" using H inj_image_mem_iff prm_apply_injective prm_set_def by metis
    hence "y \<noteq> a" and "y \<noteq> b" using assms by auto
    hence "x = y" using prm_unit_inaction `x = [a \<leftrightarrow> b] $ y` by metis
    thus "x \<in> S" using `y \<in> S` by auto
  qed
  show "S \<subseteq> [a \<leftrightarrow> b] {$} S" proof
    fix x
    assume H: "x \<in> S"
    hence "x \<noteq> a" and "x \<noteq> b" using assms by auto
    hence "x = [a \<leftrightarrow> b] $ x" using prm_unit_inaction by metis
    thus "x \<in> [a \<leftrightarrow> b] {$} S" unfolding prm_set_def using H by simp
  qed
qed

lemma prm_set_unit_action:
  assumes "a \<in> S" and "b \<notin> S"
  shows "[a \<leftrightarrow> b] {$} S = S - {a} \<union> {b}"
proof
  show "[a \<leftrightarrow> b] {$} S \<subseteq> S - {a} \<union> {b}" proof
    fix x
    assume H: "x \<in> [a \<leftrightarrow> b] {$} S"
    from this obtain y where "x = [a \<leftrightarrow> b] $ y" unfolding prm_set_def using imageE by metis
    hence "y \<in> S" using H inj_image_mem_iff prm_apply_injective prm_set_def by metis
    hence "y \<noteq> b" using assms by auto
    consider "y = a" | "y \<noteq> a" by auto
    thus "x \<in> S - {a} \<union> {b}" proof(cases)
      case 1
        hence "x = b" using `x = [a \<leftrightarrow> b] $ y` using prm_unit_action by metis
        thus ?thesis by auto
      next
      case 2
        hence "x = y" using `x = [a \<leftrightarrow> b] $ y` using prm_unit_inaction `y \<noteq> b` by metis
        hence "x \<in> S" and "x \<noteq> a" using `y \<in> S` `y \<noteq> a` by auto
        thus ?thesis by auto
      next
    qed
  qed
  show "S - {a} \<union> {b} \<subseteq> [a \<leftrightarrow> b] {$} S" proof
    fix x
    assume H: "x \<in> S - {a} \<union> {b}"
    hence "x \<noteq> a" using assms by auto
    consider "x = b" | "x \<noteq> b" by auto
    thus "x \<in> [a \<leftrightarrow> b] {$} S" proof(cases)
      case 1
        hence "x = [a \<leftrightarrow> b] $ a" using prm_unit_action by metis
        thus ?thesis using `a \<in> S` prm_set_membership by metis
      next
      case 2
        hence "x \<in> S" using H by auto
        moreover have "x = [a \<leftrightarrow> b] $ x" using prm_unit_inaction `x \<noteq> a` `x \<noteq> b` by metis
        ultimately show ?thesis using prm_set_membership by metis
      next
    qed
  qed
qed

lemma prm_set_distributes_union:
  shows "\<pi> {$} (S \<union> T) = (\<pi> {$} S) \<union> (\<pi> {$} T)"
unfolding prm_set_def by auto

lemma prm_set_distributes_difference:
  shows "\<pi> {$} (S - T) = (\<pi> {$} S) - (\<pi> {$} T)"
unfolding prm_set_def using prm_apply_injective image_set_diff by metis

definition prm_disagreement :: "'a prm \<Rightarrow> 'a prm \<Rightarrow> 'a set" ("ds") where
  "prm_disagreement \<pi> \<sigma> == {x. \<pi> $ x \<noteq> \<sigma> $ x}"

lemma prm_disagreement_ext:
  shows "x \<in> ds \<pi> \<sigma> \<equiv> \<pi> $ x \<noteq> \<sigma> $ x"
using assms unfolding prm_disagreement_def by simp

lemma prm_disagreement_composition:
  assumes "a \<noteq> b" "b \<noteq> c" "a \<noteq> c"
  shows "ds ([a \<leftrightarrow> b] \<diamondop> [b \<leftrightarrow> c]) [a \<leftrightarrow> c] = {a, b}"
using assms unfolding prm_disagreement_def by(transfer, metis preprm_disagreement_composition)

lemma prm_compose_push:
  shows "\<pi> \<diamondop> [a \<leftrightarrow> b] = [\<pi> $ a \<leftrightarrow> \<pi> $ b] \<diamondop> \<pi>"
by(transfer, metis preprm_compose_push)

end